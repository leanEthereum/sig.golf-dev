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
`KEYGEN_SECONDS` or `SIGN_SECONDS` with the hash function the submission declares for `H`. -/

def KEYGEN_SECONDS : Nat := 60
def SIGN_SECONDS : Nat := 2

/-- The hash function a hardware-track submission declares for `H`; only budgets depend on it. -/
inductive HashFunction where
  | blake2s | sha256
  deriving DecidableEq

inductive Device where
  /-- A Ledger Nano S+-class secure element (ST33). -/
  | constrained
  /-- A laptop CPU. -/
  | laptop
  deriving DecidableEq

/-- Compressions per second as `(numerator, denominator)`. The laptop's SHA-256 rate keeps the
secure element's SHA-256 to BLAKE2s ratio, 25 : 33. -/
def Device.rate : Device → HashFunction → Nat × Nat
  | .constrained, .blake2s => (33000, 1)
  | .constrained, .sha256 => (25000, 1)
  | .laptop, .blake2s => (250000000, 1)
  | .laptop, .sha256 => (250000000 * 25, 33)

/-- Whole compressions in `seconds`, rounded down. -/
def Device.compressions (device : Device) (hash : HashFunction) (seconds : Nat) : Nat :=
  seconds * (device.rate hash).1 / (device.rate hash).2

/-- Signing requests on the `constrained` track: fewer signatures for cheaper keygen and signing,
the trade hypertree pruning makes. -/
def CONSTRAINED_LIFETIME : Nat := 2 ^ 16

/-- The `laptop` track's cycle limit, high enough for its keygen budget at 8 cycles per
compression. -/
def LAPTOP_CYCLE_LIMIT : Nat := 2 ^ 40

/-- What a track fixes: the honest budgets in compressions, the signing requests the adversary may
make, and the cycle limit. -/
structure Rules where
  keygenBudget : Nat
  signBudget : Nat
  expandBudget : Nat
  lifetime : Nat
  cycleLimit : Nat

/-- `Program.budget` under `rules`. -/
def Rules.budget (rules : Rules) : Program → Option Nat
  | .keygen => some rules.keygenBudget
  | .sign => some rules.signBudget
  | .expand => some rules.expandBudget
  | .verify => none

def Rules.full : Rules := ⟨BUDGET_KEYGEN, BUDGET_SIGN, BUDGET_EXPAND, LIFETIME, CYCLE_LIMIT⟩

/-- A hardware track for the declared hash; `expand` keeps `BUDGET_EXPAND`. -/
def Device.rules (device : Device) (hash : HashFunction) : Rules where
  keygenBudget := device.compressions hash KEYGEN_SECONDS
  signBudget := device.compressions hash SIGN_SECONDS
  expandBudget := BUDGET_EXPAND
  lifetime := match device with
    | .constrained => CONSTRAINED_LIFETIME
    | .laptop => LIFETIME
  cycleLimit := match device with
    | .constrained => CYCLE_LIMIT
    | .laptop => LAPTOP_CYCLE_LIMIT

end SigGolf
