import SigGolf.Programs
import VCVio.OracleComp.QueryTracking.LoggingOracle

/-! # Security

The forgery experiment. An adaptive adversary receives the public key and cache, queries the hash
and a signing oracle that accepts any cache, and finally submits either a witness for an unsigned
message or a signature pair the oracle never returned. The oracle counts every hash call in the
experiment, honest or not, toward the budget `Q`; the signing oracle logs every request.

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

/-- The signing oracle answers a request with the signature, or `none` if the signer fails. -/
abbrev SigningSpec (sizes : Sizes) := SigningRequest sizes →ₒ Option (Bytes sizes.signature)

/-- The two final-submission forms: a witness for a fresh message, or a signature pair the oracle never returned. -/
inductive Forgery (sizes : Sizes) where
  | witness (message : Message) (witness : Bytes sizes.witness)
  | signature (message : Message) (signature : Bytes sizes.signature)

/-- A classical adversary: given the public key and cache, a computation over coins, the hash, and signing that ends by submitting a forgery, or by giving up with `none`. Local computation is unrestricted; only oracle answers and coins reveal information. -/
abbrev Adversary (sizes : Sizes) :=
  PublicKey → Bytes sizes.cache → OracleComp (World + SigningSpec sizes) (Option (Forgery sizes))

/-- Sign with the original secret key and the supplied cache, logging each request and its answer. All signing work, including any internal search, is charged like any other hash call. -/
def Submission.signingOracle (submission : Submission) (secretKey : SecretKey) :
    QueryImpl (SigningSpec submission.sizes)
      (WriterT (QueryLog (SigningSpec submission.sizes)) (OracleComp World)) :=
  QueryImpl.withLogging fun request =>
    liftM ((fun result => result.value) <$>
      submission.run .sign (secretKey, request.cache, request.message) : OracleComp HashSpec _)

namespace SigningLog
variable {sizes : Sizes}

/-- At most `LIFETIME` requests, failed ones included. -/
def Valid (log : QueryLog (SigningSpec sizes)) : Prop := log.length ≤ LIFETIME

instance (log : QueryLog (SigningSpec sizes)) : Decidable (Valid log) :=
  inferInstanceAs (Decidable (log.length ≤ LIFETIME))

/-- Some returned signature has this message. -/
def Signed (log : QueryLog (SigningSpec sizes)) (message : Message) : Prop :=
  ∃ entry ∈ log, entry.1.message = message ∧ entry.2.isSome = true

instance (log : QueryLog (SigningSpec sizes)) (message : Message) : Decidable (Signed log message) :=
  inferInstanceAs (Decidable (∃ entry ∈ log, entry.1.message = message ∧ entry.2.isSome = true))

/-- The signer returned exactly this pair. -/
def Contains (log : QueryLog (SigningSpec sizes)) (message : Message)
    (signature : Bytes sizes.signature) : Prop :=
  ∃ entry ∈ log, entry.1.message = message ∧ entry.2 = some signature

instance (log : QueryLog (SigningSpec sizes)) (message : Message) (signature : Bytes sizes.signature) :
    Decidable (Contains log message signature) :=
  inferInstanceAs (Decidable (∃ entry ∈ log, entry.1.message = message ∧ entry.2 = some signature))

end SigningLog

/-- Whether a submission passes the original public key's checks and is fresh with respect to the log. -/
def Submission.checkForgery (submission : Submission) (pk : PublicKey)
    (log : QueryLog (SigningSpec submission.sizes)) : Forgery submission.sizes → OracleComp HashSpec Bool
  | .witness message witness => do
      let verify ← submission.run .verify (message, pk, witness)
      return verify.value.isSome && decide (¬ SigningLog.Signed log message)
  | .signature message signature => do
      let expand ← submission.run .expand (message, pk, signature)
      let some witness := expand.value | return false
      let verify ← submission.run .verify (message, pk, witness)
      return verify.value.isSome && decide (¬ SigningLog.Contains log message signature)

/-- Sample the key, run keygen, let the adversary interact with the shared oracles and the logged signer, then judge: a win needs at most `LIFETIME` requests and a fresh, verified submission. -/
noncomputable def Submission.game (submission : Submission) (adversary : Adversary submission.sizes) :
    OracleComp World Bool := do
  let secretKey ← liftM sampleSecretKey
  let keygen ← liftM (submission.run .keygen secretKey)
  let some (pk, cache) := keygen.value | return false
  let (final, log) ← (simulateQ
    (QueryImpl.ofLift World (WriterT (QueryLog (SigningSpec submission.sizes)) (OracleComp World)) +
      submission.signingOracle secretKey) (adversary pk cache)).run
  let some forgery := final | return false
  let forged ← liftM (submission.checkForgery pk log forgery)
  return decide (SigningLog.Valid log) && forged

/-- Run from an empty oracle cache, recording success and the total number of hash calls: key generation, signing, the adversary's own queries, and the final check. -/
noncomputable def Submission.securityExperiment (submission : Submission)
    (adversary : Adversary submission.sizes) : ProbComp (Bool × Nat) :=
  (simulateQ countedOracle (submission.game adversary)).run.run' ∅

/-- Both final-submission forms and every total-call budget, for every adversary. There is no bound on attacker computation or private randomness. -/
def Submission.Security (submission : Submission) : Prop :=
  ∀ (adversary : Adversary submission.sizes) (Q : Nat), 1 ≤ Q →
    Pr[fun result => result.1 = true ∧ result.2 ≤ Q | submission.securityExperiment adversary]
      ≤ (Q : ENNReal) / 2 ^ SECURITY_BITS

end SigGolf
