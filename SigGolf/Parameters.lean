import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
import VCVio.OracleComp.Constructions.SampleableType
import VCVio.EvalDist.BitVec
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace SigGolf

def BUDGET_KEYGEN : Nat := 2 ^ 20
def BUDGET_SIGN : Nat := 2 ^ 17
def BUDGET_EXPAND : Nat := 2 ^ 20
def LIFETIME : Nat := 2 ^ 32
def SECURITY_BITS : Nat := 127
def CYCLE_LIMIT : Nat := 2 ^ 32
def MEMORY_BYTES : Nat := 2 ^ 24
def MAX_IMAGE_BYTES : Nat := 2 ^ 20
def MAX_CACHE_BYTES : Nat := 2 ^ 17
def MAX_SIGNATURE_BYTES : Nat := 2 ^ 14
def MAX_WITNESS_BYTES : Nat := 2 ^ 17
noncomputable def FAILURE : ENNReal := 1 / 2 ^ 128

abbrev Byte := BitVec 8
abbrev Bytes (n : Nat) := BitVec (8 * n)
abbrev SecretKey := Bytes 32
abbrev Message := Bytes 32
abbrev PublicKey := Bytes 16

inductive Phase where
  | keygen | sign | expand | verify
  deriving DecidableEq, Repr

def Phase.budget : Phase → Nat
  | .keygen => BUDGET_KEYGEN
  | .sign => BUDGET_SIGN
  | .expand => BUDGET_EXPAND
  | .verify => 0

def Phase.budgeted : List Phase := [.keygen, .sign, .expand]

/-- Submission-chosen object sizes in bytes: signature `S`, witness `W`, and cache `K`. -/
structure Sizes where
  signature : Nat
  witness : Nat
  cache : Nat
  deriving DecidableEq, Repr

/-- One set of byte offsets shared by all four programs. -/
structure Layout where
  message : Nat
  secretKey : Nat
  publicKey : Nat
  cache : Nat
  signature : Nat
  witness : Nat
  deriving DecidableEq, Repr

def Sizes.Valid (sizes : Sizes) : Prop :=
  1 ≤ sizes.signature ∧ sizes.signature ≤ MAX_SIGNATURE_BYTES ∧ sizes.witness ≤ MAX_WITNESS_BYTES ∧
    sizes.cache ≤ MAX_CACHE_BYTES

/-- Verification is also charged one cycle per started 256-byte block of witness. -/
def witnessCycles (bytes : Nat) : Nat := (bytes + 255) / 256

end SigGolf
