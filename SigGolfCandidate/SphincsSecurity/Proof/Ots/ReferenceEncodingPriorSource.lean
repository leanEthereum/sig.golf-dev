import SigGolfCandidate.SphincsSecurity.Proof.Ots.EncodingTablePrior
import SigGolfCandidate.SphincsSecurity.Proof.Ots.ReferenceEncodingSource
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec UniformTableCompletion
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs Finset.univ

noncomputable def referenceEncodingTableGame {Result : Type} (observer : FrontierObserver Result)
    (inputs : Finset HashInput) (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) : SPMF (InstrumentedResult Result) := do
  let parameter ← 𝒮[sampleParameter]
  let otsSecret ← 𝒮[sampleOtsSecrets]
  let ftsSecret ← 𝒮[sampleFtsSecrets]
  let key : SecretKey := ⟨parameter, 0, otsSecret, ftsSecret⟩
  let selections ← 𝒮[FirstSuccessFamily.selected decodeEncodingOutput encodingAttemptLimit]
  let outside ← 𝒮[PMF.uniformOfFintype (NonencodingRows parameter inputs (hencoding parameter))]
  let encoding ← complete (referenceEncodingAllowed parameter (outsideGraphMessage key inputs (hencoding parameter) outside) selections)
  let result ← 𝒮[referenceEncodingRest observer key inputs (hencoding parameter) outside selections encoding dummy adversary]
  pure (parameter, selections, result)

theorem referenceEncodingTableGame_original {Result : Type} (observer : FrontierObserver Result)
    (inputs : Finset HashInput) (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (hgraph : ∀ parameter, canonicalGraphInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    referenceEncodingTableGame observer inputs hencoding dummy adversary =
      referenceInstrumentedGame observer inputs hencoding dummy adversary := by
  rw [← referenceEncodingGame_original observer inputs hencoding hgraph dummy adversary,
    referenceEncodingGame_conditioned]
  unfold referenceEncodingTableGame
  apply congrArg (𝒮[sampleParameter] >>= ·)
  funext parameter
  apply congrArg (𝒮[sampleOtsSecrets] >>= ·)
  funext otsSecret
  apply congrArg (𝒮[sampleFtsSecrets] >>= ·)
  funext ftsSecret
  apply congrArg (𝒮[FirstSuccessFamily.selected decodeEncodingOutput encodingAttemptLimit] >>= ·)
  funext selections
  apply congrArg (𝒮[PMF.uniformOfFintype (NonencodingRows parameter inputs (hencoding parameter))] >>= ·)
  funext outside
  rw [← referenceEncodingPrior_complete]
  simp only [referenceEncodingPrior, ← PMF.monad_bind_eq_bind, ← PMF.monad_map_eq_map,
    evalSPMF_bind, evalSPMF_map, bind_assoc, bind_map_left]

end SphincsSecurity.Concrete
