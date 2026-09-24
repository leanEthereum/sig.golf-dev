import SigGolfCandidate.SphincsSecurity.Proof.Forced.FtsGuessNearAssembly
import SigGolfCandidate.SphincsSecurity.Proof.Residual.Security127LargeBudget
/-!
The small-budget half of the `127`-bit claim. Below `3 * 2^114` hash queries the original SUF advantage is at most the retained residual terms plus the normalized sum, over the test positions, of the forced FTS near-certificate probabilities, each of which `nearCertificateBound` bounds. The closing arithmetic is `small_bound_le_security127`, and `security127_of_large_budget` covers the remaining budgets.
-/

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal

theorem security128_of_small_budget (q : Nat) (hq : 1 ≤ q) (hsmall : q ≤ budgetSplit) (adversary : Adversary)
    (hbound : HasHashQueryBound scheme adversary q) : forgeAdvantage scheme adversary ≤ (q : ENNReal) / 2 ^ 128 := by
  have hbudget : q ≤ 2 ^ 127 := hsmall.trans budgetSplit_le
  have hslots : (∑ slot ∈ Finset.range q, Pr[fun hit => hit = true | FtsGuessHash.forcedNearGame fixedReferenceDummy adversary slot]) ≤
      (q : ENNReal) * nearCertificateBound q := by
    refine (Finset.sum_le_card_nsmul _ _ _ fun slot _ =>
      FtsGuessHash.forcedNearGame_le fixedReferenceDummy adversary q hbound hbudget slot).trans ?_
    rw [Finset.card_range, nsmul_eq_mul]
  have hden : ((2 ^ 160 - q : Nat) : ENNReal)⁻¹ ≤ ((2 ^ 128 - q : Nat) : ENNReal)⁻¹ := by
    apply ENNReal.inv_le_inv.mpr
    exact_mod_cast (show 2 ^ 128 - q ≤ 2 ^ 160 - q by omega)
  refine (forgeAdvantage_le_forcedNear_small_budget fixedReferenceDummy (fun _ _ _ => fixedReferenceDummyWord_valid) adversary q hbound
    hsmall).trans ?_
  refine (add_le_add le_rfl (mul_le_mul' hden hslots)).trans ?_
  exact small_bound_le_security128 q hq hsmall

theorem security127_of_small_budget (q : Nat) (hq : 1 ≤ q) (hsmall : q ≤ budgetSplit) (adversary : Adversary)
    (hbound : HasHashQueryBound scheme adversary q) : forgeAdvantage scheme adversary ≤ (q : ENNReal) / 2 ^ 127 :=
  (security128_of_small_budget q hq hsmall adversary hbound).trans (by
    apply ENNReal.div_le_div_left
    norm_num)

/-- The tighter bound needed when the final 16-byte public-key commitment adds one collision event. -/
theorem security128_below_trivial_budget (q : Nat) (hq : 1 ≤ q) (hmax : q ≤ 2 ^ 127)
    (adversary : Adversary) (hbound : HasHashQueryBound scheme adversary q) :
    forgeAdvantage scheme adversary ≤ (q : ENNReal) / 2 ^ 128 := by
  by_cases hsmall : q ≤ budgetSplit
  · exact security128_of_small_budget q hq hsmall adversary hbound
  · exact security128_of_large_budget q (by omega) hmax adversary hbound

/-- `127` bits of classical strong unforgeability for the concrete SPHINCS instance: every adversary whose whole experiment makes at most `q ≥ 1` hash queries forges with probability at most `q / 2^127`. -/
theorem security127 : HasClassicalSecurityBits scheme 127 := by
  intro q hq adversary hbound
  rw [Nat.cast_pow, Nat.cast_ofNat]
  by_cases hsmall : q ≤ budgetSplit
  · exact security127_of_small_budget q hq hsmall adversary hbound
  · exact security127_of_large_budget q (by omega) adversary hbound

end SphincsSecurity.Concrete
