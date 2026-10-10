import SigGolf.Statements

/-! # Tracks

The `constrained` and `laptop` tracks restate `Programs`, `Security`, and `Statements` under a
track's `Rules`: its budgets, `lifetime`, and `cycleLimit` replace `BUDGET_KEYGEN`, `BUDGET_SIGN`,
`BUDGET_EXPAND`, `LIFETIME`, and `CYCLE_LIMIT`. Each definition copies the original of the same
name and changes only those constants, so under `Rules.full` it unfolds to the original, which
`SigGolfTests` checks. A hardware-track certificate is
`(Device.rules device hash).Certificate submission C`. -/

namespace SigGolf.Rules
open OracleComp OracleSpec OracleComp.EvalDist

variable (rules : Rules)

/-! ### Programs -/

/-- `Submission.run`, cut off after `rules.cycleLimit` instructions. -/
def run (submission : Submission) (program : Program) (input : Input submission.sizes program) :
    OracleComp HashSpec (RunResult (Output submission.sizes program)) := do
  let execution ←
    Riscv.execute (submission.image program) rules.cycleLimit (initialState submission program input)
  let output := readOutput submission.sizes submission.layout program execution.state
  return ⟨if execution.exit = .success then some output else none,
    execution.cycles, execution.compressions⟩

/-- `Submission.honest` with `run`. -/
def honest (submission : Submission) (secretKey : SecretKey) (message : Message) :
    OracleComp HashSpec HonestResult := do
  let mut charges : Program → Nat := fun _ => 0
  -- 1. keygen
  let keygen ← rules.run submission .keygen secretKey
  charges := Function.update charges .keygen keygen.compressions
  let some (pk, cache) := keygen.output
    | return { success := false, compressions := charges, verificationCycles := 0 }
  -- 2. sign
  let sign ← rules.run submission .sign (secretKey, cache, message)
  charges := Function.update charges .sign sign.compressions
  let some signature := sign.output
    | return { success := false, compressions := charges, verificationCycles := 0 }
  -- 3. expand
  let expand ← rules.run submission .expand (message, pk, signature)
  charges := Function.update charges .expand expand.compressions
  let some witness := expand.output
    | return { success := false, compressions := charges, verificationCycles := 0 }
  -- 4. verify
  let verify ← rules.run submission .verify (message, pk, witness)
  charges := Function.update charges .verify verify.compressions
  return { success := verify.output.isSome, compressions := charges,
           verificationCycles := verify.cycles + witnessCharge submission.sizes.witness }

/-- `Submission.everyMessageSucceeds` with `honest`. -/
noncomputable def everyMessageSucceeds (submission : Submission) (secretKey : SecretKey) :
    OracleComp HashSpec Bool := do
  let mut allSucceeded := true
  for message in (Finset.univ : Finset Message).toList do
    let result ← rules.honest submission secretKey message
    allSucceeded := allSucceeded && result.success
  return allSucceeded

/-! ### Security -/

/-- `Submission.signingOracle` with `run`. -/
def signingOracle (submission : Submission) (secretKey : SecretKey) :
    QueryImpl (SigningSpec submission.sizes)
      (WriterT (SigningLog submission.sizes) (OracleComp World)) :=
  QueryImpl.withLogging fun request => do
    let run ← liftM (rules.run submission .sign (secretKey, request.cache, request.message))
    return run.output

def interact (submission : Submission) (secretKey : SecretKey)
    (adversary : Adversary submission.sizes) (pk : PublicKey)
    (cache : Bytes submission.sizes.cache) :
    OracleComp World (Option (Forgery submission.sizes) × SigningLog submission.sizes) :=
  (simulateQ (QueryImpl.ofLift World (WriterT (SigningLog submission.sizes) (OracleComp World)) +
    rules.signingOracle submission secretKey) (adversary pk cache)).run

def checkForgery (submission : Submission) (pk : PublicKey)
    (log : SigningLog submission.sizes) : Forgery submission.sizes → OracleComp HashSpec Bool
  | .witness message witness => do
      let verify ← rules.run submission .verify (message, pk, witness)
      return verify.output.isSome && decide (¬ log.Signed message)
  | .signature message signature => do
      let expand ← rules.run submission .expand (message, pk, signature)
      let some witness := expand.output | return false
      let verify ← rules.run submission .verify (message, pk, witness)
      return verify.output.isSome && decide (¬ log.Contains message signature)

/-- `Submission.game`, allowing `rules.lifetime` signing requests. -/
def game (submission : Submission) (adversary : Adversary submission.sizes) :
    OracleComp World Bool := do
  -- 1. the secret key
  let secretKey ← liftM ($ᵗ SecretKey : ProbComp SecretKey)
  -- 2. keygen; a failure is not a win
  let keygen ← liftM (rules.run submission .keygen secretKey)
  let some (pk, cache) := keygen.output | return false
  -- 3. the adversary's queries
  let (final, log) ← rules.interact submission secretKey adversary pk cache
  -- 4. the final submission
  let some forgery := final | return false
  let forged ← liftM (rules.checkForgery submission pk log forgery)
  return decide (log.length ≤ rules.lifetime) && forged

def securityExperiment (submission : Submission) (adversary : Adversary submission.sizes) :
    ProbComp (Bool × Nat) :=
  (simulateQ countedOracle (rules.game submission adversary)).run.run' ∅

/-! ### Statements -/

def Completeness (submission : Submission) : Prop :=
  ∀ secretKey,
    1 - FAILURE ≤ Pr[= true | withRandomOracle (rules.everyMessageSucceeds submission secretKey)]

/-- `E_{H,M}[2^(N_P / BUDGET_P)] ≤ 2` with the track's budgets. -/
def CompressionBudgets (submission : Submission) : Prop :=
  ∀ secretKey program (budget : Nat), rules.budget program = some budget →
    expectedValue (do let message ← ($ᵗ Message : ProbComp Message)
                      withRandomOracle (rules.honest submission secretKey message))
      (fun result => (2 : ENNReal) ^ ((result.compressions program : ℝ) / budget)) ≤ 2

def VerificationCycles (submission : Submission) (C : Nat) : Prop :=
  ∀ (hash : Hash) secretKey message,
    let result := evalWithAnswerFn hash (rules.honest submission secretKey message)
    result.success = true → result.verificationCycles ≤ C

def Security (submission : Submission) : Prop :=
  ∀ (adversary : Adversary submission.sizes) (Q : Nat), 1 ≤ Q →
    Pr[fun (won, calls) => won = true ∧ calls ≤ Q | rules.securityExperiment submission adversary]
      ≤ (Q : ENNReal) / 2 ^ SECURITY_BITS

def Termination (submission : Submission) : Prop :=
  ∀ (hash : Hash) (program : Program) (input : Input submission.sizes program),
    (evalWithAnswerFn hash (rules.run submission program input)).cycles < rules.cycleLimit

/-- The claim on a track: the score is `S × C`, as on `full`. -/
structure Certificate (submission : Submission) (C : Nat) : Prop where
  admission : submission.Admission
  completeness : rules.Completeness submission
  compressionBudgets : rules.CompressionBudgets submission
  verificationCycles : rules.VerificationCycles submission C
  security : rules.Security submission
  termination : rules.Termination submission

end SigGolf.Rules
