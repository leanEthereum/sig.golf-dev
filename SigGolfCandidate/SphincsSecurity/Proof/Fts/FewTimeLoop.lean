import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Fts.FewTimeUniform
import SigGolfCandidate.SphincsSecurity.Proof.Fts.MessagePrehit
import SigGolfCandidate.SphincsSecurity.Proof.Fts.SignerDigestSource
/-!
# Fresh successful digest attempts

An inadmissible answer already cached at a message-digest input remains there throughout the retry
loop and prevents that randomizer from being selected. Consequently, if the randomizer eventually
selected by the loop was absent from the initial cache, its successful attempt queried a fresh
input.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

set_option maxRecDepth 100000

theorem signAttempt_result_of_cached (secretKey : SecretKey) (message : Message)
    (randomness : Randomness) (beforeCache afterCache : QueryCache HashSpec)
    (attempt : Option (Index × (IndexGroup → FtsLeaf))) (output : HashOutput)
    (hcached : afterCache (tweakableHashInput secretKey.parameter .message
      (messageDigestPayload secretKey.root message randomness)) = some output)
    (hmem : (attempt, afterCache) ∈ support
      ((simulateQ (randomOracle : QueryImpl HashSpec
        (StateT (QueryCache HashSpec) ProbComp))
        (signAttempt secretKey message randomness)).run beforeCache)) :
    attempt = signAttemptResultOfOutput output := by
  obtain ⟨_, f, hf, heval⟩ := exists_answerFn_agrees_final_of_mem_support
    (signAttempt secretKey message randomness) beforeCache attempt afterCache hmem
  have hfinput : f (tweakableHashInput secretKey.parameter .message
      (messageDigestPayload secretKey.root message randomness)) = output :=
    hf hcached
  simp only [signAttempt, messageDigest, oracleHash, evalWithAnswerFn_bind,
    evalWithAnswerFn_query, hfinput] at heval
  simp only [signAttemptResultOfOutput]
  simp only [evalWithAnswerFn_pure] at heval
  by_cases hadmissible : Admissible (truncateMessageDigest output)
  · simpa [hadmissible, evalWithAnswerFn_pure] using heval.symm
  · simpa [hadmissible, evalWithAnswerFn_pure] using heval.symm

end SphincsSecurity.Concrete
