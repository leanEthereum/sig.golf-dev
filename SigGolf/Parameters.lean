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
budget keygen and sign by what a device hashes in 60 s and 2 s, rounded to powers of two. As on
`full`, `H` is an unnamed random oracle. -/

inductive Device where
  /-- A Ledger Nano S+: an ST33K1M5 secure element, a Cortex-M35P at 63 MHz. -/
  | constrained
  /-- One laptop core. -/
  | laptop
  deriving DecidableEq

/-- The Nano S+ hashes about 18,500 compressions per second inside an app: Blockstream's
SLH-DSA-SHA2-128s keygen and signing timings give 18,480. So 2^20 compressions take 57 s and 2^15
take 1.8 s. -/
def NANO_BUDGET_KEYGEN : Nat := 2 ^ 20
def NANO_BUDGET_SIGN : Nat := 2 ^ 15

/-- At 63 MHz, 2^32 cycles take 68 s and 2^27 take 2.1 s, so work besides hashing also fits. -/
def NANO_CYCLE_LIMIT_KEYGEN : Nat := 2 ^ 32
def NANO_CYCLE_LIMIT_SIGN : Nat := 2 ^ 27

/-- An app's SRAM on the Nano S+, from the Ledger SDK's `nanos2` linker script. -/
def NANO_RAM_BYTES : Nat := 40 * 1024

/-- An app's flash on the Nano S+, code and data, from the same linker script. -/
def NANO_FLASH_BYTES : Nat := 400 * 1024

/-- Signing requests on the `constrained` track: fewer signatures for cheaper keygen and signing,
the trade hypertree pruning makes. -/
def CONSTRAINED_LIFETIME : Nat := 2 ^ 16

/-- The overuse margin on `constrained`: with 16 times `CONSTRAINED_LIFETIME` signing requests, a
forgery still has probability at most `Q / 2 ^ OVERUSE_SECURITY_BITS`. -/
def OVERUSE_LIFETIME : Nat := 2 ^ 20
def OVERUSE_SECURITY_BITS : Nat := 96

/-- One laptop core hashes about 2^25 compressions per second: 2^24.3 measured with SHA-NI on an
Intel Core Ultra 7 155H, about 2^25.4 on an Apple M2. So 2^31 take 64 s and 2^26 take 2 s. -/
def LAPTOP_BUDGET_KEYGEN : Nat := 2 ^ 31
def LAPTOP_BUDGET_SIGN : Nat := 2 ^ 26

/-- The `laptop` track's cycle limit for keygen and sign, far above its keygen budget at 8 cycles
per compression. -/
def LAPTOP_CYCLE_LIMIT : Nat := 2 ^ 40

/-- The memory keygen and sign may use on a device: RAM is the addresses below `ramBytes`, and
`flashBytes` holds both programs and the cache. -/
structure DeviceMemory where
  ramBytes : Nat
  flashBytes : Nat

/-- What a track fixes: the honest budgets in compressions, the signing requests the adversary may
make, each program's cycle limit, the device memory keygen and sign run in, if any, and an
overuse margin `(lifetime, bits)`, if any: a weaker security bound for a larger lifetime. -/
structure Rules where
  keygenBudget : Nat
  signBudget : Nat
  expandBudget : Nat
  lifetime : Nat
  cycleLimit : Program → Nat
  memory : Option DeviceMemory
  overuse : Option (Nat × Nat)

/-- `Program.budget` under `rules`. -/
def Rules.budget (rules : Rules) : Program → Option Nat
  | .keygen => some rules.keygenBudget
  | .sign => some rules.signBudget
  | .expand => some rules.expandBudget
  | .verify => none

def Rules.full : Rules :=
  ⟨BUDGET_KEYGEN, BUDGET_SIGN, BUDGET_EXPAND, LIFETIME, fun _ => CYCLE_LIMIT, none, none⟩

/-- A hardware track. `expand` and `verify` keep `full`'s budget and cycle limit: they run on
the verifier's side, not on the device. -/
def Device.rules : Device → Rules
  | .constrained =>
    { keygenBudget := NANO_BUDGET_KEYGEN
      signBudget := NANO_BUDGET_SIGN
      expandBudget := BUDGET_EXPAND
      lifetime := CONSTRAINED_LIFETIME
      cycleLimit := fun
        | .keygen => NANO_CYCLE_LIMIT_KEYGEN
        | .sign => NANO_CYCLE_LIMIT_SIGN
        | .expand | .verify => CYCLE_LIMIT
      memory := some ⟨NANO_RAM_BYTES, NANO_FLASH_BYTES⟩
      overuse := some (OVERUSE_LIFETIME, OVERUSE_SECURITY_BITS) }
  | .laptop =>
    { keygenBudget := LAPTOP_BUDGET_KEYGEN
      signBudget := LAPTOP_BUDGET_SIGN
      expandBudget := BUDGET_EXPAND
      lifetime := LIFETIME
      cycleLimit := fun
        | .keygen | .sign => LAPTOP_CYCLE_LIMIT
        | .expand | .verify => CYCLE_LIMIT
      memory := none
      overuse := none }

end SigGolf
