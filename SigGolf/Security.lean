import SigGolf.Programs

/-! # Security

The forgery experiment. An adaptive adversary receives the public key and cache, queries the hash
and a signing oracle that accepts any cache, and finally submits either a witness for an unsigned
message or a signature pair the oracle never returned. Every hash call in the experiment, honest
or not, counts toward its budget `Q`. -/

namespace SigGolf
open OracleComp OracleSpec

/-- A signing query: the message and the cache the attacker chooses to supply. -/
structure SigningRequest (sizes : Sizes) where
  message : Message
  cache : Bytes sizes.cache

/-- The attacker supplies only the message and cache. All signing work, including any internal search, is charged. -/
def Submission.signingOracle (submission : Submission) (secretKey : SecretKey)
    (request : SigningRequest submission.sizes) : OracleComp HashSpec (RunResult (Bytes submission.sizes.signature)) :=
  submission.run .sign (secretKey, request.cache, request.message)

/-- The two final-submission forms: a witness for a fresh message, or a signature pair the oracle never returned. -/
inductive Forgery (sizes : Sizes) where
  | witness (message : Message) (witness : Bytes sizes.witness)
  | signature (message : Message) (signature : Bytes sizes.signature)

/-- One step of a strategy: submit, query the hash, request a signature, draw coins, or continue. -/
inductive Action (sizes : Sizes) (state : Type) where
  | submit (candidate : Forgery sizes)
  | hash (input : Query) (resume : BitVec 256 → state)
  | sign (request : SigningRequest sizes) (resume : Option (Bytes sizes.signature) → state)
  | sample (n : Nat) (resume : Fin (n + 1) → state)
  | step (next : state)

/-- A classical interactive strategy. Only oracle responses and private coins reveal new information. Local computation is unrestricted. -/
structure Adversary (sizes : Sizes) where
  State : Type
  initial : PublicKey → Bytes sizes.cache → State
  step : State → Action sizes State

/-- What the experiment remembers: returned signatures, request count, and total hash calls. -/
structure Transcript (sizes : Sizes) where
  signed : List (Message × Bytes sizes.signature) := []
  signingRequests : Nat := 0
  hashCalls : Nat := 0

/-- Failed signing requests consume a slot and hash calls but add no replay entry. -/
def Transcript.record {sizes : Sizes} (transcript : Transcript sizes) (message : Message)
    (result : RunResult (Bytes sizes.signature)) : Transcript sizes :=
  { signed := match result.value with
      | none => transcript.signed
      | some signature => (message, signature) :: transcript.signed
    signingRequests := transcript.signingRequests + 1
    hashCalls := transcript.hashCalls + result.hashCalls }

/-- Whether the final submission won, and the total hash calls at that point. -/
structure AttackResult where
  won : Bool
  hashCalls : Nat
  deriving DecidableEq, Repr

/-- No returned signature has this message. -/
def Transcript.freshMessage {sizes : Sizes} (transcript : Transcript sizes) (message : Message) : Bool :=
  !transcript.signed.any (fun entry => entry.1 == message)

/-- This exact pair was never returned. -/
def Transcript.freshSignature {sizes : Sizes} (transcript : Transcript sizes)
    (message : Message) (signature : Bytes sizes.signature) : Bool :=
  !transcript.signed.contains (message, signature)

/-- The final checker uses the original public key. All its hash calls are charged, including failed expansion or verification. -/
def Submission.checkForgery (submission : Submission) (pk : PublicKey)
    (transcript : Transcript submission.sizes) : Forgery submission.sizes → OracleComp HashSpec AttackResult
  | .witness message witness => do
      let verify ← submission.run .verify (message, pk, witness)
      return ⟨verify.value.isSome && transcript.freshMessage message,
        transcript.hashCalls + verify.hashCalls⟩
  | .signature message signature => do
      let expand ← submission.run .expand (message, pk, signature)
      let calls := transcript.hashCalls + expand.hashCalls
      let some witness := expand.value | return ⟨false, calls⟩
      let verify ← submission.run .verify (message, pk, witness)
      return ⟨verify.value.isSome && transcript.freshSignature message signature,
        calls + verify.hashCalls⟩

/-- `rounds` is how many steps we watch. The adversary may run longer, but it wins only by submitting within them, and `Security` demands the bound at every `rounds`. -/
def Submission.interact (submission : Submission) (adversary : Adversary submission.sizes)
    (secretKey : SecretKey) (pk : PublicKey) : Nat → adversary.State → Transcript submission.sizes →
      OracleComp World AttackResult
  | 0, _, transcript => pure ⟨false, transcript.hashCalls⟩
  | rounds + 1, state, transcript =>
      match adversary.step state with
      | .submit candidate => liftM (submission.checkForgery pk transcript candidate)
      | .hash input resume => do
          let answer ← liftM (HashSpec.query input)
          submission.interact adversary secretKey pk rounds (resume answer)
            { transcript with hashCalls := transcript.hashCalls + 1 }
      | .sign request resume => do
          if transcript.signingRequests < LIFETIME then
            let result ← liftM (submission.signingOracle secretKey request)
            submission.interact adversary secretKey pk rounds (resume result.value)
              (transcript.record request.message result)
          else return ⟨false, transcript.hashCalls⟩
      | .sample n resume => do
          let answer ← liftM (unifSpec.query n)
          submission.interact adversary secretKey pk rounds (resume answer) transcript
      | .step next => submission.interact adversary secretKey pk rounds next transcript

/-- Sample the key and oracle, run keygen, hand the adversary the public key and cache, then interact. -/
noncomputable def Submission.securityExperiment (submission : Submission)
    (adversary : Adversary submission.sizes) (rounds : Nat) : ProbComp AttackResult :=
  withRandomness do
    let secretKey ← liftM sampleSecretKey
    let keygen ← liftM (submission.run .keygen secretKey)
    let some (pk, cache) := keygen.value | return ⟨false, keygen.hashCalls⟩
    submission.interact adversary secretKey pk rounds (adversary.initial pk cache)
      { hashCalls := keygen.hashCalls }

/-- Both final-submission forms, every total-call budget, and every finite prefix of every adaptive strategy. There is no bound on attacker computation or private randomness. -/
def Submission.Security (submission : Submission) : Prop :=
  ∀ (adversary : Adversary submission.sizes) (rounds Q : Nat), 1 ≤ Q →
    Pr[fun result => result.won = true ∧ result.hashCalls ≤ Q |
      submission.securityExperiment adversary rounds] ≤ (Q : ENNReal) / 2 ^ SECURITY_BITS

end SigGolf
