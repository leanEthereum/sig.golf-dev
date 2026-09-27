import SigGolf.Security
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Statements

Five of the six statements a certificate proves; `Security` is in `Security.lean`. Each is a
proposition about one `Submission`, and `Certificate submission C` lists all six in README order
for the claimed verification bound `C`. Probabilities and expectations live in `ENNReal`, the
nonnegative reals with infinity. -/

namespace SigGolf
open OracleComp OracleComp.EvalDist

/-- Declared sizes within bounds, image-size limits, and 8-byte-aligned, nonoverlapping buffers below embedded data. -/
def Submission.Admission (submission : Submission) : Prop :=
  submission.sizes.Valid ∧ ∀ phase, (submission.image phase).Valid submission.sizes submission.layout

/-- One shared oracle makes the pipeline succeed for every message, except with probability `FAILURE`. The secret key is universally quantified, not averaged. -/
def Submission.Completeness (submission : Submission) : Prop :=
  ∀ secretKey, 1 - FAILURE ≤ Pr[fun ok => ok = true | withRandomOracle (submission.allSucceed secretKey)]

/-- `2 ^ (cost / budget)` with real division, as an extended nonnegative real. -/
noncomputable def budgetMoment (cost budget : Nat) : ENNReal :=
  ENNReal.ofReal ((2 : ℝ) ^ ((cost : ℝ) / (budget : ℝ)))

/-- For an independent uniform message and random oracle, the expected `2 ^ (cost / budget)` of each budgeted program is at most 2. Failed phases are charged; unreached phases cost zero. -/
def Submission.CompressionBudgets (submission : Submission) : Prop :=
  ∀ secretKey phase (budget : Nat), phase.budget = some budget →
    expectedValue (submission.honestWorkload secretKey)
      (fun result => budgetMoment (result.costs phase) budget) ≤ 2

/-- Scored cycles: verification's RISC-V cycles plus the witness charge, on every successful honest pipeline. Arbitrary witnesses remain subject to `Termination`. -/
def Submission.VerificationCycles (submission : Submission) (C : Nat) : Prop :=
  ∀ (hash : Hash) secretKey message,
    let result := submission.honestWith hash secretKey message
    result.success = true → result.verificationCycles ≤ C

/-- Every program halts in fewer than `CYCLE_LIMIT` cycles on every typed input and every fixed oracle, including arbitrary caches, signatures, and witnesses. An unfinished observation cannot satisfy this statement. -/
def Submission.Termination (submission : Submission) : Prop :=
  ∀ (hash : Hash) (phase : Phase) (input : Input submission.sizes phase),
    let result := submission.runWith hash phase input
    result.finished = true ∧ result.cycles < CYCLE_LIMIT

/-- The competition claim for the exact four images, declared sizes, shared layout, and claimed cycle bound `C`. The score is `S × C` for the declared signature size `S`. The loader and interpreter enforce fixed-size outputs, memory limits, and fresh stateless executions. -/
structure Certificate (submission : Submission) (C : Nat) : Prop where
  admission : submission.Admission
  completeness : submission.Completeness
  compressionBudgets : submission.CompressionBudgets
  verificationCycles : submission.VerificationCycles C
  security : submission.Security
  termination : submission.Termination

end SigGolf
