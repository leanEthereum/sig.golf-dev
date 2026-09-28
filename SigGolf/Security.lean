import SigGolf.Programs

/-! # Security

The forgery experiment. An adaptive adversary receives the public key and cache, queries the hash
and a signing oracle that accepts any cache, and finally submits either a witness for an unsigned
message or a signature pair the oracle never returned. Every hash call in the experiment, honest
or not, counts toward its budget `Q`.

The adversary is an `OracleComp` over coins, the hash, and signing: a computation that makes
finitely many queries and then submits a forgery or gives up. A strategy that could run for ever
is represented by its truncations, which give up where they are cut. Giving up never wins, and
such a strategy's win probability is the limit of its truncations', so a bound over all
adversaries bounds every adaptive strategy. -/

namespace SigGolf
open OracleComp OracleSpec

/-- A signing query: the message and the cache the attacker chooses to supply. -/
structure SigningRequest (sizes : Sizes) where
  message : Message
  cache : Bytes sizes.cache

/-- The attacker supplies only the message and cache. All signing work, including any internal search, is charged. -/
def Submission.signingOracle (submission : Submission) (secretKey : SecretKey)
    (request : SigningRequest submission.sizes) :
    OracleComp HashSpec (RunResult (Bytes submission.sizes.signature)) :=
  submission.run .sign (secretKey, request.cache, request.message)

/-- The adversary's oracles: private coins, the hash, and signing. -/
abbrev AttackSpec (sizes : Sizes) := World + (SigningRequest sizes →ₒ Option (Bytes sizes.signature))

/-- The two final-submission forms: a witness for a fresh message, or a signature pair the oracle never returned. -/
inductive Forgery (sizes : Sizes) where
  | witness (message : Message) (witness : Bytes sizes.witness)
  | signature (message : Message) (signature : Bytes sizes.signature)

/-- A classical adversary: given the public key and cache, a computation over its oracles that ends by submitting a forgery, or by giving up with `none`. Local computation is unrestricted; only oracle answers and coins reveal information. -/
abbrev Adversary (sizes : Sizes) :=
  PublicKey → Bytes sizes.cache → OracleComp (AttackSpec sizes) (Option (Forgery sizes))

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

/-- No returned signature has this message. -/
def Transcript.freshMessage {sizes : Sizes} (transcript : Transcript sizes) (message : Message) : Bool :=
  !transcript.signed.any (fun entry => entry.1 == message)

/-- This exact pair was never returned. -/
def Transcript.freshSignature {sizes : Sizes} (transcript : Transcript sizes)
    (message : Message) (signature : Bytes sizes.signature) : Bool :=
  !transcript.signed.contains (message, signature)

/-- How the experiment answers the adversary while threading the transcript. Coins and hash queries go to the shared oracles, each hash query charged one call. Signing runs `sign` with the original secret key and the supplied cache; a request beyond `LIFETIME` ends the experiment. -/
def Submission.oracles (submission : Submission) (secretKey : SecretKey) :
    QueryImpl (AttackSpec submission.sizes)
      (OptionT (StateT (Transcript submission.sizes) (OracleComp World)))
  | .inl (.inl n) => OptionT.lift (StateT.lift (liftM (unifSpec.query n)))
  | .inl (.inr input) => do
      modify fun transcript => { transcript with hashCalls := transcript.hashCalls + 1 }
      OptionT.lift (StateT.lift (liftM (HashSpec.query input)))
  | .inr request => do
      let transcript ← get
      if transcript.signingRequests < LIFETIME then
        let result ← OptionT.lift (StateT.lift (liftM (submission.signingOracle secretKey request)))
        set (transcript.record request.message result)
        return result.value
      else failure

/-- Whether the final submission won, and the total hash calls at that point. -/
structure AttackResult where
  won : Bool
  hashCalls : Nat
  deriving DecidableEq, Repr

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

/-- Sample the key and oracle, run keygen, hand the adversary the public key and cache, let it interact, then check what it submitted. Giving up, or exceeding the signing lifetime, is not a win. -/
noncomputable def Submission.securityExperiment (submission : Submission)
    (adversary : Adversary submission.sizes) : ProbComp AttackResult :=
  withRandomness do
    let secretKey ← liftM sampleSecretKey
    let keygen ← liftM (submission.run .keygen secretKey)
    let some (pk, cache) := keygen.value | return ⟨false, keygen.hashCalls⟩
    let (outcome, transcript) ← (simulateQ (submission.oracles secretKey) (adversary pk cache)).run.run
      { hashCalls := keygen.hashCalls }
    match outcome with
    | some (some forgery) => liftM (submission.checkForgery pk transcript forgery)
    | _ => return ⟨false, transcript.hashCalls⟩

/-- Both final-submission forms and every total-call budget, for every adversary. There is no bound on attacker computation or private randomness. -/
def Submission.Security (submission : Submission) : Prop :=
  ∀ (adversary : Adversary submission.sizes) (Q : Nat), 1 ≤ Q →
    Pr[fun result => result.won = true ∧ result.hashCalls ≤ Q | submission.securityExperiment adversary]
      ≤ (Q : ENNReal) / 2 ^ SECURITY_BITS

end SigGolf
