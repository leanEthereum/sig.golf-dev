import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Fintype.Basic

/-! # Parameters

The competition's constants, its byte types, the four programs, what a submission declares (its
object sizes and one memory layout), and the tracks. Read this file first; `Oracle`, `Riscv`,
`Programs`, `Security`, `Statements`, and `Tracks` build on it in that order. -/

namespace SigGolf

/-! ### Honest budgets, in 64-byte hash compressions -/

def BUDGET_KEYGEN : Nat := 2 ^ 20
def BUDGET_SIGN : Nat := 2 ^ 17
def BUDGET_EXPAND : Nat := 2 ^ 20

/-! ### Security -/

/-- Signing requests the adversary may make. -/
def LIFETIME : Nat := 2 ^ 32

/-- When the whole experiment makes at most `Q` hash calls, honest ones included, a forgery has
probability at most `Q / 2 ^ SECURITY_BITS`. -/
def SECURITY_BITS : Nat := 127

/-- Allowed probability, over the oracle, that some honest message fails. -/
noncomputable def FAILURE : ENNReal := 1 / 2 ^ 128

/-! ### Machine and object limits -/

/-- Every program halts below this many cycles. Execution is also cut off after this many
instructions, which loses nothing since each instruction costs at least one cycle. -/
def CYCLE_LIMIT : Nat := 2 ^ 32

/-- Data memory, 16 MiB. -/
def MEMORY_BYTES : Nat := 2 ^ 24

/-- Bound on `4 × instructions + embedded data bytes` per program. -/
def MAX_PROGRAM_BYTES : Nat := 2 ^ 20

def MAX_CACHE_BYTES : Nat := 2 ^ 17

def MAX_WITNESS_BYTES : Nat := 2 ^ 17

def MAX_SIGNATURE_BYTES : Nat := 2 ^ 14

/-! ### Objects -/

abbrev Byte := BitVec 8

/-- `n` bytes as one little-endian bit vector. -/
abbrev Bytes (n : Nat) := BitVec (8 * n)
abbrev SecretKey := Bytes 32
abbrev Message := Bytes 32
abbrev PublicKey := Bytes 16

inductive Program where
  | keygen | sign | expand | verify
  deriving DecidableEq

instance : Fintype Program :=
  ⟨{.keygen, .sign, .expand, .verify}, fun program => by cases program <;> simp⟩

def Program.budget : Program → Option Nat
  | .keygen => some BUDGET_KEYGEN
  | .sign => some BUDGET_SIGN
  | .expand => some BUDGET_EXPAND
  | .verify => none

/-- The README's `S`, `W`, and `K`, in bytes. -/
structure Sizes where
  signature : Nat
  witness : Nat
  cache : Nat
  deriving DecidableEq

/-- One set of byte offsets shared by all four programs. -/
structure Layout where
  message : Nat
  secretKey : Nat
  publicKey : Nat
  cache : Nat
  signature : Nat
  witness : Nat
  deriving DecidableEq

abbrev Sizes.Valid (sizes : Sizes) : Prop :=
  sizes.signature ≤ MAX_SIGNATURE_BYTES ∧ sizes.witness ≤ MAX_WITNESS_BYTES ∧
    sizes.cache ≤ MAX_CACHE_BYTES

/-- `⌈bytes / 256⌉`: verification pays one cycle per started 256-byte block of witness. -/
def witnessCharge (bytes : Nat) : Nat := (bytes + 255) / 256

/-! ### Tracks

`Statements` uses the constants above, the `full` track's. The `constrained` and `laptop` tracks
price keygen and sign on a device instead: a budget is the compressions the device completes in
`KEYGEN_SECONDS` or `SIGN_SECONDS`. As on `full`, `H` is an unnamed random oracle. -/

def KEYGEN_SECONDS : Nat := 60
def SIGN_SECONDS : Nat := 2

inductive Device where
  /-- A Ledger Nano S+: an ST33K1M5 secure element, a Cortex-M35P at 63 MHz. -/
  | constrained
  /-- A laptop CPU with SHA-256 instructions (Intel SHA-NI, ARMv8 SHA2). -/
  | laptop
  deriving DecidableEq

/-- Compressions per second with the device's fastest hash. The secure element has no hash
hardware, and BLAKE2s is fastest in software; the laptop's SHA-256 instructions make the SHA-256
compression function 5/2 times faster than BLAKE2s, at 250,000,000. -/
def Device.rate : Device → Nat
  | .constrained => 33000
  | .laptop => 625000000

/-- Whole compressions in `seconds`. -/
def Device.compressions (device : Device) (seconds : Nat) : Nat :=
  seconds * device.rate

/-- An app's SRAM on the Nano S+, from the Ledger SDK's `nanos2` linker script. -/
def NANO_RAM_BYTES : Nat := 40 * 1024

/-- An app's flash on the Nano S+, code and data, from the same linker script. -/
def NANO_FLASH_BYTES : Nat := 400 * 1024

/-- The Nano S+ clock: keygen and sign run at most this many cycles per second. -/
def NANO_HZ : Nat := 63000000

/-- Signing requests on the `constrained` track: fewer signatures for cheaper keygen and signing,
the trade hypertree pruning makes. -/
def CONSTRAINED_LIFETIME : Nat := 2 ^ 16

/-- The `laptop` track's cycle limit for keygen and sign, high enough for its keygen budget at 8
cycles per compression. -/
def LAPTOP_CYCLE_LIMIT : Nat := 2 ^ 40

/-- The memory keygen and sign may use on a device: RAM is the addresses below `ramBytes`, and
`flashBytes` holds both programs and the cache. -/
structure DeviceMemory where
  ramBytes : Nat
  flashBytes : Nat

/-- What a track fixes: the honest budgets in compressions, the signing requests the adversary may
make, each program's cycle limit, and the device memory keygen and sign run in, if any. -/
structure Rules where
  keygenBudget : Nat
  signBudget : Nat
  expandBudget : Nat
  lifetime : Nat
  cycleLimit : Program → Nat
  memory : Option DeviceMemory

/-- `Program.budget` under `rules`. -/
def Rules.budget (rules : Rules) : Program → Option Nat
  | .keygen => some rules.keygenBudget
  | .sign => some rules.signBudget
  | .expand => some rules.expandBudget
  | .verify => none

def Rules.full : Rules :=
  ⟨BUDGET_KEYGEN, BUDGET_SIGN, BUDGET_EXPAND, LIFETIME, fun _ => CYCLE_LIMIT, none⟩

/-- A hardware track. `expand` and `verify` keep `full`'s budget and cycle limit: they run on
the verifier's side, not on the device. -/
def Device.rules (device : Device) : Rules where
  keygenBudget := device.compressions KEYGEN_SECONDS
  signBudget := device.compressions SIGN_SECONDS
  expandBudget := BUDGET_EXPAND
  lifetime := match device with
    | .constrained => CONSTRAINED_LIFETIME
    | .laptop => LIFETIME
  cycleLimit program := match device, program with
    | .constrained, .keygen => KEYGEN_SECONDS * NANO_HZ
    | .constrained, .sign => SIGN_SECONDS * NANO_HZ
    | .laptop, .keygen | .laptop, .sign => LAPTOP_CYCLE_LIMIT
    | _, .expand | _, .verify => CYCLE_LIMIT
  memory := match device with
    | .constrained => some ⟨NANO_RAM_BYTES, NANO_FLASH_BYTES⟩
    | .laptop => none

end SigGolf
