import SigGolfCandidate.SphincsSecurity.Proof.Residual.RetainedResidualCacheTail
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option exponentiation.threshold 1024

private theorem largeRangeClosing (x : ℝ) (hx : 3 / 16384 ≤ x) :
    2 * (x / 2 ^ 32) - (x / 2 ^ 32) ^ 2 + (12 / 65536) * x +
      (x / 2 ^ 27 + 1 / 2 ^ 700) ≤ x := by
  have hn : 0 ≤ x := le_trans (by norm_num) hx
  have htail : (1 : ℝ) / 2 ^ 700 ≤ x / 2 ^ 40 := by
    have hsmall : (1 : ℝ) / 2 ^ 700 ≤ (3 / 16384) / 2 ^ 40 := by norm_num
    nlinarith
  have hsquare := sq_nonneg (x / 2 ^ 32)
  norm_num at hx htail ⊢
  nlinarith [hn, htail, hsquare]

theorem native_bound_le_security128 (q : Nat) (hlarge : budgetSplit ≤ q) (hsmall : q ≤ 2 ^ 127) :
    ENNReal.ofReal (2 * ((q : ℝ) / 2 ^ digestBits) - ((q : ℝ) / 2 ^ digestBits) ^ 2) +
      (q : ENNReal) * fullCertificateTotalRate +
      ((q : ENNReal) * certificateCacheExceptionRate + proposalPrefixExceptionBound) ≤ (q : ENNReal) / 2 ^ 128 := by
  rw [budgetSplit_def] at hlarge
  refine le_trans (add_le_add le_rfl (add_le_add (mul_le_mul' le_rfl certificateCacheExceptionRate_le) le_rfl)) ?_
  rw [fullCertificateTotalRate_def, fullCertificateExcessRate_def, proposalPrefixExceptionBound_def]
  have hrate : (2 ^ 144 : ENNReal)⁻¹ + 11 / 2 ^ 144 = 12 / 2 ^ 144 := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    norm_num [ENNReal.toReal_inv, ENNReal.toReal_div]
  rw [hrate]
  let x : ℝ := (q : ℝ) / 2 ^ 128
  have hx : 3 / 16384 ≤ x := by
    have hq : (3 * 2 ^ 114 : ℝ) ≤ q := by exact_mod_cast hlarge
    apply (le_div_iff₀ (by positivity)).mpr
    norm_num at hq ⊢
    exact hq
  have hn : 0 ≤ x := by positivity
  have hu : x ≤ 1 / 2 := by
    have hq : (q : ℝ) ≤ 2 ^ 127 := by exact_mod_cast hsmall
    apply (div_le_iff₀ (by positivity)).mpr
    norm_num at hq ⊢
    exact hq
  have hp : 0 ≤ 2 * ((q : ℝ) / 2 ^ digestBits) - ((q : ℝ) / 2 ^ digestBits) ^ 2 := by
    have hq' : (q : ℝ) / 2 ^ digestBits ≤ 1 := by
      apply (div_le_iff₀ (by positivity)).mpr
      simpa only [one_mul] using (calc
        (q : ℝ) ≤ 2 ^ 127 := by exact_mod_cast hsmall
        _ ≤ 2 ^ digestBits := by norm_num [digestBits])
    have hq : 0 ≤ (q : ℝ) / 2 ^ digestBits := by positivity
    nlinarith [mul_nonneg hq (sub_nonneg.mpr hq')]
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  repeat rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  rw [ENNReal.toReal_ofReal hp]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_natCast, ENNReal.toReal_ofNat]
  convert largeRangeClosing x hx using 1 <;> dsimp only [x, digestBits] <;> norm_num <;> ring

theorem security128_of_large_budget (q : Nat) (hlarge : budgetSplit ≤ q) (hsmall : q ≤ 2 ^ 127)
    (adversary : Adversary) (hcost : HasHashQueryBound scheme adversary q) :
    forgeAdvantage scheme adversary ≤ (q : ENNReal) / 2 ^ 128 :=
  (RetainedResidual.forgeAdvantage_le_native_bound fixedReferenceDummy
    (fun _ _ _ => fixedReferenceDummyWord_valid) adversary q hcost hsmall).trans
      (native_bound_le_security128 q hlarge hsmall)

theorem security127_of_large_budget (q : Nat) (hlarge : budgetSplit ≤ q) (adversary : Adversary)
    (hcost : HasHashQueryBound scheme adversary q) : forgeAdvantage scheme adversary ≤ (q : ENNReal) / 2 ^ 127 := by
  by_cases hsmall : q ≤ 2 ^ 127
  · exact (security128_of_large_budget q hlarge hsmall adversary hcost).trans (by
          apply ENNReal.div_le_div_left
          norm_num)
  · apply probOutput_le_one.trans
    calc
      (1 : ENNReal) = (2 ^ 127 : ENNReal) / 2 ^ 127 := (ENNReal.div_self (by positivity) (by finiteness)).symm
      _ ≤ _ := ENNReal.div_le_div_right (by exact_mod_cast (show 2 ^ 127 ≤ q by omega)) _

end SphincsSecurity.Concrete
