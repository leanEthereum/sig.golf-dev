import SigGolf.Security

/-! # Statements

The six statements a certificate proves, in the order the README lists them, and the certificate
itself. `expectedValue c g` is the expectation of `g result` over the computation `c`;
probabilities and expectations live in `ENNReal`, the nonnegative reals with infinity. -/

namespace SigGolf
open OracleComp OracleComp.EvalDist

/-- **Admission.** Sizes within bounds; each image within the size limit, with aligned,
nonoverlapping buffers below its data. -/
def Submission.Admission (submission : Submission) : Prop :=
  submission.sizes.Valid ∧
    ∀ program, (submission.image program).Valid submission.sizes submission.layout

instance (submission : Submission) : Decidable submission.Admission := by
  unfold Submission.Admission; infer_instance

/-- **Completeness.** -/
def Submission.Completeness (submission : Submission) : Prop :=
  ∀ secretKey,
    1 - FAILURE ≤ Pr[= true | withRandomOracle (submission.everyMessageSucceeds secretKey)]

/-- **Compression budgets:** `E_{H,M}[2^(N_P / BUDGET_P)] ≤ 2`. -/
def Submission.CompressionBudgets (submission : Submission) : Prop :=
  ∀ secretKey program (budget : Nat), program.budget = some budget →
    expectedValue (do let message ← ($ᵗ Message : ProbComp Message)
                      withRandomOracle (submission.honest secretKey message))
      (fun result => (2 : ENNReal) ^ ((result.compressions program : ℝ) / budget)) ≤ 2

/-- **Verification cycles.** Only honest witnesses are bounded here; arbitrary ones fall
under `Termination`. -/
def Submission.VerificationCycles (submission : Submission) (C : Nat) : Prop :=
  ∀ (hash : Hash) secretKey message,
    let result := evalWithAnswerFn hash (submission.honest secretKey message)
    result.success = true → result.verificationCycles ≤ C

/-- **Security.** No bound on the adversary's computation or private randomness; only hash calls
count. -/
def Submission.Security (submission : Submission) : Prop :=
  ∀ (adversary : Adversary submission.sizes) (Q : Nat), 1 ≤ Q →
    Pr[fun (won, calls) => won = true ∧ calls ≤ Q | submission.securityExperiment adversary]
      ≤ (Q : ENNReal) / 2 ^ SECURITY_BITS

/-- **Termination.** Inputs include arbitrary caches, signatures, and witnesses. A run cut off at
`CYCLE_LIMIT` instructions has spent at least that many cycles, so it never satisfies this. -/
def Submission.Termination (submission : Submission) : Prop :=
  ∀ (hash : Hash) (program : Program) (input : Input submission.sizes program),
    (evalWithAnswerFn hash (submission.run program input)).cycles < CYCLE_LIMIT

/-- The score is `S × C` for the declared signature size `S` and the certified cycle bound `C`. -/
structure Certificate (submission : Submission) (C : Nat) : Prop where
  admission : submission.Admission
  completeness : submission.Completeness
  compressionBudgets : submission.CompressionBudgets
  verificationCycles : submission.VerificationCycles C
  security : submission.Security
  termination : submission.Termination

end SigGolf
