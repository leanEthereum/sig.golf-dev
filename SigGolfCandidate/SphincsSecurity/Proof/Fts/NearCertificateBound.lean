import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Fts.FixedProposalMoments
import SigGolfCandidate.SphincsSecurity.Proof.Fts.TerminalProposalEnvelope

namespace SphincsSecurity.Concrete

open ENNReal

set_option maxHeartbeats 2000000 in
theorem stirlingPowerMoment_twentythree_le :
    stirlingPowerMoment (19 / 50) 23 ≤ (2 ^ 44 : ENNReal) := by
  unfold stirlingPowerMoment
  apply (ENNReal.toReal_le_toReal (ENNReal.sum_ne_top.mpr (fun _ _ => by finiteness)) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_sum, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_ofNat]
  norm_num [Finset.sum_range_succ, Nat.stirlingSecond]

/-- The average price, over a uniform proposal word of the fixed length, of a certificate that covers all trees but one. -/
theorem uniformWordAverage_nearPrice (required : Finset FtsTree) (hdegree : required.card + 1 = Fintype.card FtsTree) :
    uniformWordAverage fixedProposalLength (terminalCertificatePrice required) ≤
      nearCertificatePrice := by
  rw [nearCertificatePrice_def]
  replace hdegree : required.card = 23 := by
    have htrees : Fintype.card FtsTree = 24 := Fintype.card_fin _
    omega
  have hprice : terminalCertificatePrice required = fun word =>
      ((((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) * targetCertificateScale required) *
        proposalPowerSum required.card word := by
    funext word
    unfold terminalCertificatePrice proposalPowerSum
    ring
  rw [hprice, uniformWordAverage_mul_left]
  refine (mul_le_mul' le_rfl (uniformWordAverage_powerSum_le (α := Index) fixedProposalLength required.card (19 / 50)
    fixedProposalLength_rate_le)).trans ?_
  rw [hdegree]
  refine (mul_le_mul' le_rfl (mul_le_mul' le_rfl stirlingPowerMoment_twentythree_le)).trans ?_
  unfold targetCertificateScale
  rw [hdegree]
  have hindex : Fintype.card Index = 2 ^ 34 := Fintype.card_fin _
  have hleaf : Fintype.card FtsLeaf = 2 ^ 8 := Fintype.card_fin _
  rw [hindex, hleaf]
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  norm_num [ftsTreeHeight, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_div, ENNReal.toReal_pow]

end SphincsSecurity.Concrete
