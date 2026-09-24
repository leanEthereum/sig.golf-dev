import SigGolfCandidate.SphincsSecurity.Proof.Ots.ReferenceEncodingErasure
import SigGolfCandidate.SphincsSecurity.Proof.Ots.EncodingConditionalObservation
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs Finset.univ referenceEncodingRest

noncomputable def referenceEncodingGame {Result : Type} (observer : FrontierObserver Result)
    (inputs : Finset HashInput) (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) : SPMF (InstrumentedResult Result) := do
  let parameter ← 𝒮[sampleParameter]
  let otsSecret ← 𝒮[sampleOtsSecrets]
  let ftsSecret ← 𝒮[sampleFtsSecrets]
  let key : SecretKey := ⟨parameter, 0, otsSecret, ftsSecret⟩
  let reference ← 𝒮[referenceFamilyOracleSample key inputs (hencoding parameter)]
  let result ← 𝒮[referenceEncodingRest observer key inputs (hencoding parameter)
    (fun cell => reference.2 cell.val) reference.1
    (reference.2 ∘ encodingInputCell parameter inputs (hencoding parameter)) dummy adversary]
  pure (parameter, reference.1, result)

theorem referenceEncodingGame_original {Result : Type} (observer : FrontierObserver Result)
    (inputs : Finset HashInput) (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (hgraph : ∀ parameter, canonicalGraphInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    referenceEncodingGame observer inputs hencoding dummy adversary =
      referenceInstrumentedGame observer inputs hencoding dummy adversary := by
  unfold referenceEncodingGame referenceInstrumentedGame
  apply congrArg (𝒮[sampleParameter] >>= ·)
  funext parameter
  apply congrArg (𝒮[sampleOtsSecrets] >>= ·)
  funext otsSecret
  apply congrArg (𝒮[sampleFtsSecrets] >>= ·)
  funext ftsSecret
  apply evalSPMF_bind_congr (m := SPMF)
  intro reference hreference
  have hselected := referenceFamilyOracleSample_selections ⟨parameter, 0, otsSecret, ftsSecret⟩ inputs
    (hencoding parameter) (hgraph parameter) reference
    (by simpa only [PMF.evalSPMF_eq, SPMF.support_eq_support, SPMF.support_liftM] using hreference)
  dsimp only
  rw [referenceEncodingRest_table observer ⟨parameter, 0, otsSecret, ftsSecret⟩ inputs
    (hencoding parameter) (hgraph parameter) reference.1 reference.2 hselected.symm dummy adversary]

private theorem join_comp {Index Cell Answer : Type} (embed : Index → Cell) (hinj : Function.Injective embed)
    (rows : Index → Answer) (outside : UniformTableSplit.Outside embed → Answer) :
    UniformTableSplit.join embed hinj rows outside ∘ embed = rows :=
  funext fun index => UniformTableSplit.join_embed embed hinj rows outside index

private theorem join_outside {Index Cell Answer : Type} (embed : Index → Cell) (hinj : Function.Injective embed)
    (rows : Index → Answer) (outside : UniformTableSplit.Outside embed → Answer) :
    (fun cell : UniformTableSplit.Outside embed => UniformTableSplit.join embed hinj rows outside cell.val) = outside :=
  funext fun cell => UniformTableSplit.join_outside embed hinj rows outside cell

theorem referenceEncodingRest_join {Result : Type} (observer : FrontierObserver Result)
    (key : SecretKey) (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
    (outside : NonencodingRows key.parameter inputs hencoding) (selections : ReferenceFamily)
    (encoding : canonicalEncodingInputs key.parameter → HashOutput)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    let table := joinEncodingTable key.parameter inputs hencoding encoding outside
    referenceEncodingRest observer key inputs hencoding (fun cell => table cell.val) selections
        (table ∘ encodingInputCell key.parameter inputs hencoding) dummy adversary =
      referenceEncodingRest observer key inputs hencoding outside selections encoding dummy adversary := by
  have hout : (fun cell : UniformTableSplit.Outside (encodingInputCell key.parameter inputs hencoding) =>
      joinEncodingTable key.parameter inputs hencoding encoding outside cell.val) = outside :=
    join_outside (encodingInputCell key.parameter inputs hencoding)
      (encodingInputCell_injective key.parameter inputs hencoding) encoding outside
  have hin : joinEncodingTable key.parameter inputs hencoding encoding outside ∘
      encodingInputCell key.parameter inputs hencoding = encoding :=
    join_comp (encodingInputCell key.parameter inputs hencoding)
      (encodingInputCell_injective key.parameter inputs hencoding) encoding outside
  exact congrArg₂ (fun outside encoding =>
    referenceEncodingRest observer key inputs hencoding outside selections encoding dummy adversary) hout hin

theorem referenceEncodingGame_conditioned {Result : Type} (observer : FrontierObserver Result)
    (inputs : Finset HashInput) (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    referenceEncodingGame observer inputs hencoding dummy adversary = (do
      let parameter ← 𝒮[sampleParameter]
      let otsSecret ← 𝒮[sampleOtsSecrets]
      let ftsSecret ← 𝒮[sampleFtsSecrets]
      let key : SecretKey := ⟨parameter, 0, otsSecret, ftsSecret⟩
      let selections ← 𝒮[FirstSuccessFamily.selected decodeEncodingOutput encodingAttemptLimit]
      let outside ← 𝒮[PMF.uniformOfFintype (NonencodingRows parameter inputs (hencoding parameter))]
      let rows ← 𝒮[FirstSuccessFamily.afterSelect decodeEncodingOutput encodingAttemptLimit selections]
      let remaining ← 𝒮[PMF.uniformOfFintype (UniformTableSplit.Outside
        (referenceFamilyCell parameter (outsideGraphMessage key inputs (hencoding parameter) outside)) → HashOutput)]
      let encoding := UniformTableSplit.join
        (referenceFamilyCell parameter (outsideGraphMessage key inputs (hencoding parameter) outside))
        (referenceFamilyCell_injective parameter (outsideGraphMessage key inputs (hencoding parameter) outside))
        (Function.uncurry rows) remaining
      let result ← 𝒮[referenceEncodingRest observer key inputs (hencoding parameter) outside selections encoding dummy adversary]
      pure (parameter, selections, result)) := by
  simp only [referenceEncodingGame, referenceFamilyOracleSample, ← PMF.monad_bind_eq_bind,
    ← PMF.monad_map_eq_map, evalSPMF_bind, evalSPMF_map, bind_assoc, bind_map_left,
    referenceFamilyOracleTable]
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
  apply congrArg (𝒮[FirstSuccessFamily.afterSelect decodeEncodingOutput encodingAttemptLimit selections] >>= ·)
  funext rows
  apply congrArg (𝒮[PMF.uniformOfFintype (UniformTableSplit.Outside
    (referenceFamilyCell parameter (outsideGraphMessage ⟨parameter, 0, otsSecret, ftsSecret⟩ inputs
      (hencoding parameter) outside)) → HashOutput)] >>= ·)
  funext remaining
  rw [referenceEncodingRest_join observer ⟨parameter, 0, otsSecret, ftsSecret⟩ inputs
    (hencoding parameter) outside selections _ dummy adversary]

end SphincsSecurity.Concrete
