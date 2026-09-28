import SigGolf.Security

/-! # Statements

The six statements a certificate proves, in the order the README lists them, and the certificate
itself. `expectedValue c g` is the expectation of `g result` over the computation `c`;
probabilities and expectations live in `ENNReal`, the nonnegative reals with infinity. -/

namespace SigGolf
open OracleComp OracleComp.EvalDist

/-- **Admission.** Declared sizes within bounds, image-size limits, and 8-byte-aligned,
nonoverlapping buffers below embedded data. -/
def Submission.Admission (submission : Submission) : Prop :=
  submission.sizes.Valid ∧
    ∀ program, (submission.image program).Valid submission.sizes submission.layout

instance (submission : Submission) : Decidable submission.Admission := by
  unfold Submission.Admission; infer_instance

/-- **Completeness** (README 1). One shared oracle makes the experiment succeed for every message,
except with probability `FAILURE`. The secret key is universally quantified, not averaged. -/
def Submission.Completeness (submission : Submission) : Prop :=
  ∀ secretKey,
    1 - FAILURE ≤ Pr[= true | withRandomOracle (submission.everyMessageSucceeds secretKey)]

/-- **Compression budgets** (README 2). `E_{H,M}[2^(N_P / BUDGET_P)] ≤ 2` for an independent
uniform message and random oracle; failed programs are charged, unreached ones cost zero. -/
def Submission.CompressionBudgets (submission : Submission) : Prop :=
  ∀ secretKey program (budget : Nat), program.budget = some budget →
    expectedValue (do let message ← ($ᵗ Message : ProbComp Message)
                      withRandomOracle (submission.honest secretKey message))
      (fun result => (2 : ENNReal) ^ ((result.compressions program : ℝ) / budget)) ≤ 2

/-- **Verification cycles** (README 3). On every successful honest experiment, `verify`'s RISC-V
cycles plus the witness charge are at most `C`. Arbitrary witnesses remain subject to
`Termination`. -/
def Submission.VerificationCycles (submission : Submission) (C : Nat) : Prop :=
  ∀ (hash : Hash) secretKey message,
    let result := evalWithAnswerFn hash (submission.honest secretKey message)
    result.success = true → result.verificationCycles ≤ C

/-- **Security.** Both forgery forms and every total-call budget, for every adversary: winning
within `Q` hash calls has probability at most `Q / 2 ^ SECURITY_BITS`. There is no bound on the
adversary's computation or private randomness. -/
def Submission.Security (submission : Submission) : Prop :=
  ∀ (adversary : Adversary submission.sizes) (Q : Nat), 1 ≤ Q →
    Pr[fun (won, calls) => won = true ∧ calls ≤ Q | submission.securityExperiment adversary]
      ≤ (Q : ENNReal) / 2 ^ SECURITY_BITS

/-- **Termination.** Every program halts in fewer than `CYCLE_LIMIT` cycles on every typed input
and every fixed oracle, including arbitrary caches, signatures, and witnesses. A run cut off at
`CYCLE_LIMIT` instructions has spent at least that many cycles, so it never satisfies this. -/
def Submission.Termination (submission : Submission) : Prop :=
  ∀ (hash : Hash) (program : Program) (input : Input submission.sizes program),
    (evalWithAnswerFn hash (submission.run program input)).cycles < CYCLE_LIMIT

/-- The competition claim for the exact four images, declared sizes, shared layout, and claimed
cycle bound `C`. The score is `S × C` for the declared signature size `S`. -/
structure Certificate (submission : Submission) (C : Nat) : Prop where
  admission : submission.Admission
  completeness : submission.Completeness
  compressionBudgets : submission.CompressionBudgets
  verificationCycles : submission.VerificationCycles C
  security : submission.Security
  termination : submission.Termination

end SigGolf
