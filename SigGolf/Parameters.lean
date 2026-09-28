import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Fintype.Basic

/-! # Parameters

The competition's constants, its byte types, the four programs, and what a submission declares:
its object sizes and one memory layout. Read this file first; `Oracle`, `Riscv`, `Programs`,
`Security`, and `Statements` build on it in that order. -/

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

/-- Largest declarable cache. -/
def MAX_CACHE_BYTES : Nat := 2 ^ 17

/-- Largest declarable witness. -/
def MAX_WITNESS_BYTES : Nat := 2 ^ 17

/-- Largest declarable signature. -/
def MAX_SIGNATURE_BYTES : Nat := 2 ^ 14

/-! ### Objects -/

abbrev Byte := BitVec 8

/-- `n` bytes as one little-endian bit vector. -/
abbrev Bytes (n : Nat) := BitVec (8 * n)
abbrev SecretKey := Bytes 32
abbrev Message := Bytes 32
abbrev PublicKey := Bytes 16

/-- The four programs of a submission. -/
inductive Program where
  | keygen | sign | expand | verify
  deriving DecidableEq

instance : Fintype Program :=
  ⟨{.keygen, .sign, .expand, .verify}, fun program => by cases program <;> simp⟩

/-- Compression budgets of `keygen`, `sign`, and `expand`; `verify` has none. -/
def Program.budget : Program → Option Nat
  | .keygen => some BUDGET_KEYGEN
  | .sign => some BUDGET_SIGN
  | .expand => some BUDGET_EXPAND
  | .verify => none

/-- Submission-chosen object sizes in bytes: signature `S`, witness `W`, and cache `K`. -/
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

/-- Declared sizes within the competition bounds. -/
abbrev Sizes.Valid (sizes : Sizes) : Prop :=
  sizes.signature ≤ MAX_SIGNATURE_BYTES ∧ sizes.witness ≤ MAX_WITNESS_BYTES ∧
    sizes.cache ≤ MAX_CACHE_BYTES

/-- `⌈bytes / 256⌉`: verification pays one cycle per started 256-byte block of witness. -/
def witnessCharge (bytes : Nat) : Nat := (bytes + 255) / 256

end SigGolf
