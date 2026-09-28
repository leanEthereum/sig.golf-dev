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
adversaries bounds every adaptive strategy.

Two more VCVio pieces. `impl.withLogging` is `impl` with a `WriterT` layer that appends
`⟨query, answer⟩` to a `QueryLog` after each answered query, and running it returns the result
paired with the log. `QueryImpl.ofLift World m` forwards `World` queries unchanged into `m`. -/

namespace SigGolf
open OracleComp OracleSpec

/-! ### Oracles and adversary -/

/-- A signing query: the message and the cache the attacker chooses to supply. -/
structure SigningRequest (sizes : Sizes) where
  message : Message
  cache : Bytes sizes.cache

/-- The signing oracle answers a request with the signature, or `none` if the signer fails. -/
abbrev SigningSpec (sizes : Sizes) : OracleSpec (SigningRequest sizes) :=
  SigningRequest sizes →ₒ Option (Bytes sizes.signature)

/-- The signing oracle's transcript T: each request paired with its answer, failures included. -/
abbrev SigningLog (sizes : Sizes) := QueryLog (SigningSpec sizes)

/-- The two forgery forms: a witness for a fresh message, or a signature pair the oracle never
returned. -/
inductive Forgery (sizes : Sizes) where
  | witness (message : Message) (witness : Bytes sizes.witness)
  | signature (message : Message) (signature : Bytes sizes.signature)

/-- A classical adversary: given the public key and cache, a computation over coins, the hash,
and signing that ends by submitting a forgery, or by giving up with `none`. It queries coins as
`.inl (.inl _)`, `H` as `.inl (.inr _)`, and signing as `.inr _`. Local computation is
unrestricted; only oracle answers and coins reveal information. -/
abbrev Adversary (sizes : Sizes) :=
  PublicKey → Bytes sizes.cache →
    OracleComp (World + SigningSpec sizes) (Option (Forgery sizes))

/-- Sign with the original secret key and the supplied cache, logging each request and its
answer. All signing work, including any internal search, is charged like any other hash call. -/
def Submission.signingOracle (submission : Submission) (secretKey : SecretKey) :
    QueryImpl (SigningSpec submission.sizes)
      (WriterT (SigningLog submission.sizes) (OracleComp World)) :=
  QueryImpl.withLogging fun request =>
    liftM (RunResult.output <$>
      submission.run .sign (secretKey, request.cache, request.message) : OracleComp HashSpec _)

/-- Let the adversary interact with the shared oracles and the logged signer; returns its final
answer paired with the signing log T. -/
def Submission.interact (submission : Submission) (secretKey : SecretKey)
    (adversary : Adversary submission.sizes) (pk : PublicKey)
    (cache : Bytes submission.sizes.cache) :
    OracleComp World (Option (Forgery submission.sizes) × SigningLog submission.sizes) :=
  (simulateQ (QueryImpl.ofLift World (WriterT (SigningLog submission.sizes) (OracleComp World)) +
    submission.signingOracle secretKey) (adversary pk cache)).run

/-! ### The signing log -/

namespace SigningLog
variable {sizes : Sizes}

/-- At most `LIFETIME` requests, failed ones included. -/
abbrev WithinLifetime (log : SigningLog sizes) : Prop := log.length ≤ LIFETIME

/-- Some returned signature has this message: an entry `⟨request, answer⟩` with that message and
an answer. -/
abbrev Signed (log : SigningLog sizes) (message : Message) : Prop :=
  ∃ entry ∈ log, entry.1.message = message ∧ entry.2.isSome = true

/-- The signer returned exactly this pair. -/
abbrev Contains (log : SigningLog sizes) (message : Message) (signature : Bytes sizes.signature) :
    Prop :=
  ∃ entry ∈ log, entry.1.message = message ∧ entry.2 = some signature

end SigningLog

/-! ### The experiment -/

/-- Whether the forgery verifies under the original public key and is fresh with respect to the
log (README step 4). -/
def Submission.checkForgery (submission : Submission) (pk : PublicKey)
    (log : SigningLog submission.sizes) : Forgery submission.sizes → OracleComp HashSpec Bool
  | .witness message witness => do
      let verify ← submission.run .verify (message, pk, witness)
      return verify.output.isSome && decide (¬ log.Signed message)
  | .signature message signature => do
      let expand ← submission.run .expand (message, pk, signature)
      let some witness := expand.output | return false
      let verify ← submission.run .verify (message, pk, witness)
      return verify.output.isSome && decide (¬ log.Contains message signature)

/-- The README's security experiment, steps 1 to 4. A win needs at most `LIFETIME` requests and a
fresh, verified forgery, so making more requests loses instead of being cut off; the best win
probability over all adversaries is the same either way. Hash calls are counted in
`securityExperiment`. -/
def Submission.game (submission : Submission) (adversary : Adversary submission.sizes) :
    OracleComp World Bool := do
  -- 1. the secret key
  let secretKey ← liftM ($ᵗ SecretKey : ProbComp SecretKey)
  -- 2. keygen; a failure is not a win
  let keygen ← liftM (submission.run .keygen secretKey)
  let some (pk, cache) := keygen.output | return false
  -- 3. the adversary's queries
  let (final, log) ← submission.interact secretKey adversary pk cache
  -- 4. the final submission
  let some forgery := final | return false
  let forged ← liftM (submission.checkForgery pk log forgery)
  return decide log.WithinLifetime && forged

/-- Run from an empty oracle cache. `.run` returns `(won, hash calls)`, the calls covering key
generation, signing, the adversary's own queries, and the final check; `.run' ∅` starts `H`'s
answer table empty. -/
def Submission.securityExperiment (submission : Submission)
    (adversary : Adversary submission.sizes) : ProbComp (Bool × Nat) :=
  (simulateQ countedOracle (submission.game adversary)).run.run' ∅

end SigGolf
