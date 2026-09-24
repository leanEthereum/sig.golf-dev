import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Reference.ReferenceJointPrior
import SigGolfCandidate.SphincsSecurity.Proof.Ots.ReferencePrefixResidual
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec UniformTableCompletion ResidualTableCompletion
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false

theorem graphReferenceSample_eq_prefixAuxiliary (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) :
    graphReferenceSample parameter inputs hencoding =
      (referenceAuxiliarySample inputs).bind (fun auxiliary =>
        (PMF.uniformOfFintype CanonicalGraphLabels).map (fun labels =>
          (auxiliary.selections, (labels, canonicalPrefixResidual parameter inputs hencoding labels
            auxiliary.selections auxiliary.rows auxiliary.seed)))) := by
  rw [graphReferenceSample_eq_auxiliary]
  simp only [referenceAuxiliarySample, PMF.bind_bind, PMF.map, Function.comp_def, PMF.pure_bind]
  apply congrArg (FirstSuccessFamily.selected decodeEncodingOutput encodingAttemptLimit).bind
  funext selections
  conv_lhs => enter [2, rows]; rw [PMF.bind_comm]
  rw [PMF.bind_comm]
  conv_rhs => enter [2, rows]; rw [PMF.bind_comm]
  conv_rhs => rw [PMF.bind_comm]
  apply congrArg (PMF.uniformOfFintype CanonicalGraphLabels).bind
  funext labels
  have h := congrArg (PMF.map (fun residual => (selections, (labels, residual))))
    (canonicalReferenceResidual_prefix_law parameter inputs hencoding labels selections)
  simpa only [PMF.map, Function.comp_def, PMF.bind_bind, PMF.pure_bind] using h

theorem referenceResidualGame_eq_prefixAuxiliary (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    referenceResidualGame inputs hencoding dummy adversary = (do
      let parameter ← 𝒮[sampleParameter]
      let otsSecret ← 𝒮[sampleOtsSecrets]
      let ftsSecret ← 𝒮[sampleFtsSecrets]
      let auxiliary ← 𝒮[referenceAuxiliarySample inputs]
      let labels ← 𝒮[PMF.uniformOfFintype CanonicalGraphLabels]
      let f := programmedHash parameter otsSecret ftsSecret labels
        (finiteHashAnswer ∅ inputs (canonicalPrefixResidual parameter inputs (hencoding parameter) labels
          auxiliary.selections auxiliary.rows auxiliary.seed))
      let result ← 𝒮[referenceFamilyFrontierRest ⟨parameter, 0, otsSecret, ftsSecret⟩ f labels auxiliary.selections dummy adversary]
      pure (auxiliary.selections, result)) := by
  simp only [referenceResidualGame, graphReferenceSample_eq_prefixAuxiliary,
    ← PMF.monad_bind_eq_bind, ← PMF.monad_map_eq_map, evalSPMF_bind, evalSPMF_map, bind_assoc, bind_map_left]

noncomputable def referencePrefixCoordinateGame (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) : SPMF (ReferenceFamily × (Bool × SigningBoundaryTrace)) := do
  let parameter ← 𝒮[sampleParameter]
  let auxiliary ← 𝒮[referenceAuxiliarySample inputs]
  let words := referenceFamilyWords auxiliary.selections dummy
  let high ← 𝒮[PMF.uniformOfFintype CanonicalGraphHighHalves]
  let exposedValues ← 𝒮[PMF.uniformOfFintype (InitialPublicLabels words)]
  let labels ← complete (initialAllowed words exposedValues)
  let ots := coordinateOtsSecrets labels
  let fts := coordinateFtsSecrets labels
  let graph := coordinateGraphLabels labels high
  let f := programmedHash parameter ots fts graph
    (finiteHashAnswer ∅ inputs (canonicalPrefixResidual parameter inputs (hencoding parameter) graph
      auxiliary.selections auxiliary.rows auxiliary.seed))
  let result ← 𝒮[referenceFamilyFrontierRest ⟨parameter, 0, ots, fts⟩ f graph auxiliary.selections dummy adversary]
  pure (auxiliary.selections, result)

theorem referenceResidualGame_eq_prefixCoordinates (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    referenceResidualGame inputs hencoding dummy adversary = referencePrefixCoordinateGame inputs hencoding dummy adversary := by
  rw [referenceResidualGame_eq_prefixAuxiliary, referencePrefixCoordinateGame]
  apply congrArg (𝒮[sampleParameter] >>= ·)
  funext parameter
  conv_lhs =>
    enter [2, ots]
    rw [RetainedObservation.bind_comm 𝒮[sampleFtsSecrets] 𝒮[referenceAuxiliarySample inputs]]
  rw [RetainedObservation.bind_comm 𝒮[sampleOtsSecrets] 𝒮[referenceAuxiliarySample inputs]]
  apply congrArg (𝒮[referenceAuxiliarySample inputs] >>= ·)
  funext auxiliary
  exact sampleSecretGraph_bind_public (referenceFamilyWords auxiliary.selections dummy)
    (fun _ _ ots fts graph => do
      let f := programmedHash parameter ots fts graph
        (finiteHashAnswer ∅ inputs (canonicalPrefixResidual parameter inputs (hencoding parameter) graph
          auxiliary.selections auxiliary.rows auxiliary.seed))
      let result ← 𝒮[referenceFamilyFrontierRest ⟨parameter, 0, ots, fts⟩ f graph auxiliary.selections dummy adversary]
      pure (auxiliary.selections, result))

noncomputable def referencePrefixJointPriorGame (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) : SPMF (ReferenceFamily × (Bool × SigningBoundaryTrace)) := do
  let parameter ← 𝒮[sampleParameter]
  let encoding ← 𝒮[referenceEncodingAuxiliarySample]
  let words := referenceFamilyWords encoding.selections dummy
  let high ← 𝒮[PMF.uniformOfFintype CanonicalGraphHighHalves]
  let exposedValues ← 𝒮[PMF.uniformOfFintype (InitialPublicLabels words)]
  let labels ← complete (initialAllowed words exposedValues)
  let seed ← completeRows (fun _ : inputs => none)
  let ots := coordinateOtsSecrets labels
  let fts := coordinateFtsSecrets labels
  let graph := coordinateGraphLabels labels high
  let f := programmedHash parameter ots fts graph
    (finiteHashAnswer ∅ inputs (canonicalPrefixResidual parameter inputs (hencoding parameter) graph
      encoding.selections encoding.rows seed))
  let result ← 𝒮[referenceFamilyFrontierRest ⟨parameter, 0, ots, fts⟩ f graph encoding.selections dummy adversary]
  pure (encoding.selections, result)

theorem referencePrefixCoordinateGame_eq_jointPrior (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    referencePrefixCoordinateGame inputs hencoding dummy adversary = referencePrefixJointPriorGame inputs hencoding dummy adversary := by
  rw [referencePrefixCoordinateGame, referencePrefixJointPriorGame]
  apply congrArg (𝒮[sampleParameter] >>= ·)
  funext parameter
  rw [referenceAuxiliarySample_bind_seed]
  apply congrArg (𝒮[referenceEncodingAuxiliarySample] >>= ·)
  funext encoding
  dsimp only
  rw [RetainedObservation.bind_comm (completeRows (fun _ : inputs => none))]
  apply congrArg (𝒮[PMF.uniformOfFintype CanonicalGraphHighHalves] >>= ·)
  funext high
  rw [RetainedObservation.bind_comm (completeRows (fun _ : inputs => none))
    𝒮[PMF.uniformOfFintype (InitialPublicLabels (referenceFamilyWords encoding.selections dummy))]]
  apply congrArg (𝒮[PMF.uniformOfFintype (InitialPublicLabels (referenceFamilyWords encoding.selections dummy))] >>= ·)
  funext exposedValues
  rw [RetainedObservation.bind_comm (completeRows (fun _ : inputs => none))
    (complete (initialAllowed (referenceFamilyWords encoding.selections dummy) exposedValues))]

end SphincsSecurity.Concrete
