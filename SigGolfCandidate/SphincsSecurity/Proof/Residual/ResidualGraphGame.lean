import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Hypertree.CanonicalGraphGame
import SigGolfCandidate.SphincsSecurity.Proof.Residual.CanonicalResidualQuery
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec OracleComp.DeferredSampling
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalGraphInputs canonicalPayloadInputs canonicalGraphOrder instFintypePosition

noncomputable local instance residualGameLabelsSampleable : SampleableType CanonicalGraphLabels :=
  SampleableType.ofFintype CanonicalGraphLabels

noncomputable def residualGraphOracleGame (inputs : Finset HashInput) (dummy : OtsReferenceWords) (adversary : Adversary) :
    ProbComp (Bool × SigningBoundaryTrace) := do
  let parameter ← sampleParameter
  let otsSecret ← sampleOtsSecrets
  let ftsSecret ← sampleFtsSecrets
  let labels ← ($ᵗ CanonicalGraphLabels : ProbComp _)
  let residual ← sampleHashTable inputs
  graphFrontierGameRest parameter otsSecret ftsSecret labels
    (programmedHash parameter otsSecret ftsSecret labels (finiteHashAnswer ∅ inputs residual)) dummy adversary

theorem evalSPMF_canonicalGraph_eq_residualGraph (inputs : Finset HashInput)
    (hgraph : ∀ parameter, canonicalGraphInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    𝒮[canonicalGraphOracleGame inputs hgraph dummy adversary] =
      𝒮[residualGraphOracleGame inputs dummy adversary] := by
  rw [canonicalGraphOracleGame, residualGraphOracleGame]
  apply evalSPMF_bind_congr_left
  intro parameter
  apply evalSPMF_bind_congr_left
  intro otsSecret
  apply evalSPMF_bind_congr_left
  intro ftsSecret
  have h := evalSPMF_plantCanonicalGraph_bind_eq_residual parameter otsSecret ftsSecret inputs (hgraph parameter)
    (fun labels table => graphFrontierGameRest parameter otsSecret ftsSecret labels
      (finiteHashAnswer ∅ inputs table) dummy adversary)
  simpa only [finiteHashAnswer_program_eq] using h

theorem evalSPMF_boundaryGameCore_residualGraph (inputs : Finset HashInput)
    (hgraph : ∀ parameter, canonicalGraphInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary)
    (hinputs : hashInputs (boundaryGameCore adversary) ⊆ inputs) :
    𝒮[(simulateQ romImpl (boundaryGameCore adversary)).run' ∅] =
      𝒮[residualGraphOracleGame inputs dummy adversary] :=
  (evalSPMF_boundaryGameCore_canonicalGraph inputs hgraph dummy adversary hinputs).trans
    (evalSPMF_canonicalGraph_eq_residualGraph inputs hgraph dummy adversary)

end SphincsSecurity.Concrete
