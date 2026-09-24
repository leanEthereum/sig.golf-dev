import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Fts.UniformProposalMixedMoments
namespace SphincsSecurity.Concrete

open ENNReal

theorem stirlingPowerMoment_ne_top (rate : ENNReal) (hrate : rate ≠ ⊤) (degree : Nat) :
    stirlingPowerMoment rate degree ≠ ⊤ := by
  unfold stirlingPowerMoment
  apply ENNReal.sum_ne_top.mpr
  intro order _
  exact ENNReal.mul_ne_top (by finiteness) (ENNReal.pow_ne_top hrate)

set_option maxHeartbeats 5000000 in
theorem stirlingPowerMoment_full_mean_le :
    (2 ^ 34 : ENNReal) * (2 ^ 90 : ENNReal)⁻¹ * stirlingPowerMoment (19 / 50) 24 ≤ 1 / 5 := by
  have hm := stirlingPowerMoment_ne_top (19 / 50) (by finiteness) 24
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_div,
    ENNReal.toReal_ofNat, ENNReal.toReal_one]
  unfold stirlingPowerMoment
  rw [ENNReal.toReal_sum (fun order _ => by finiteness)]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_div, ENNReal.toReal_ofNat,
    ENNReal.toReal_natCast]
  norm_num [Finset.sum_range_succ, Nat.stirlingSecond]

set_option maxHeartbeats 5000000 in
theorem stirlingPowerMoment_full_variance_le :
    (2 ^ 34 : ENNReal) * (2 ^ 180 : ENNReal)⁻¹ * stirlingPowerMoment (19 / 50) 48 ≤ 13 / 25000 := by
  have hm := stirlingPowerMoment_ne_top (19 / 50) (by finiteness) 48
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_div,
    ENNReal.toReal_ofNat]
  unfold stirlingPowerMoment
  rw [ENNReal.toReal_sum (fun order _ => by finiteness)]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_div, ENNReal.toReal_ofNat,
    ENNReal.toReal_natCast]
  norm_num [Finset.sum_range_succ, Nat.stirlingSecond]

end SphincsSecurity.Concrete
