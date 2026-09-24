import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Residual.AdaptiveResidualErasure
import SigGolfCandidate.SphincsSecurity.Proof.Hypertree.CanonicalPublicPrior
import SigGolfCandidate.SphincsSecurity.Proof.Reference.ReferenceResidualSeeds
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec UniformTableCompletion ResidualTableCompletion
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false

structure ReferenceEncodingAuxiliary where
  selections : ReferenceFamily
  rows : CanonicalEncodingRows

noncomputable def referenceEncodingAuxiliarySample : PMF ReferenceEncodingAuxiliary :=
  (FirstSuccessFamily.selected decodeEncodingOutput encodingAttemptLimit).bind (fun selections =>
    (FirstSuccessFamily.afterSelect decodeEncodingOutput encodingAttemptLimit selections).map
      (fun rows => ⟨selections, Function.uncurry rows⟩))

theorem referenceAuxiliarySample_bind_seed {Result : Type} (inputs : Finset HashInput)
    (next : ReferenceAuxiliary inputs → SPMF Result) :
    (𝒮[referenceAuxiliarySample inputs] >>= next) =
      (𝒮[referenceEncodingAuxiliarySample] >>= fun encoding =>
        completeRows (fun _ : inputs => none) >>= fun seed => next ⟨encoding.selections, encoding.rows, seed⟩) := by
  rw [completeRows_empty]
  simp only [referenceAuxiliarySample, referenceEncodingAuxiliarySample,
    ← PMF.monad_bind_eq_bind, ← PMF.monad_map_eq_map, evalSPMF_bind,
    map_eq_bind_pure_comp, Function.comp_def, evalSPMF_pure, bind_assoc, pure_bind]

end SphincsSecurity.Concrete
