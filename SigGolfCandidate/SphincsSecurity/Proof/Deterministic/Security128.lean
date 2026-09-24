import SigGolfCandidate.SphincsSecurity.Proof.Deterministic.Security

open OracleComp OracleSpec ENNReal

namespace SphincsSecurity.Seeded

set_option backward.isDefEq.respectTransparency false

/-- The seed-programming loss fits inside one unit of the 128-bit query budget. -/
theorem seed_loss_absorbed128 (q : Nat) (hq : 1 ≤ q) (hmax : q ≤ 2 ^ 127) :
    ((q - 1 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
      ((q - 1 : Nat) : ℝ≥0∞) / ((2 ^ 256 : Nat) : ℝ≥0∞) ≤
        q / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  have hguess : ((q - 1 : Nat) : ℝ≥0∞) / ((2 ^ 256 : Nat) : ℝ≥0∞) ≤
      1 / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
    calc
      _ ≤ ((2 ^ 128 : Nat) : ℝ≥0∞) / ((2 ^ 256 : Nat) : ℝ≥0∞) :=
        ENNReal.div_le_div (by exact_mod_cast (Nat.sub_le q 1).trans (hmax.trans (by norm_num))) le_rfl
      _ ≤ ((2 ^ 128 : Nat) : ℝ≥0∞) /
          (((2 ^ 128 : Nat) : ℝ≥0∞) * ((2 ^ 128 : Nat) : ℝ≥0∞)) :=
        ENNReal.div_le_div le_rfl (by norm_num)
      _ = _ := by
        simpa only [mul_one] using ENNReal.mul_div_mul_left 1 ((2 ^ 128 : Nat) : ℝ≥0∞)
          (c := ((2 ^ 128 : Nat) : ℝ≥0∞)) (by norm_num) (ENNReal.natCast_ne_top _)
  calc
    _ ≤ ((q - 1 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
      1 / ((2 ^ 128 : Nat) : ℝ≥0∞) := add_le_add le_rfl hguess
    _ = _ := by
      rw [← ENNReal.add_div]
      congr 1
      exact_mod_cast Nat.sub_add_cancel hq

/-- The deterministic 256-bit secret-key instance keeps 128-bit internal security for every query count at which the final 127-bit target is nontrivial. -/
theorem scheme_security128_below_trivial_final (q : Nat) (hq : 1 ≤ q)
    (hmax : q ≤ 2 ^ 127) (adversary : Adversary)
    (hbound : HasHashQueryBound scheme adversary q) :
    forgeAdvantage scheme adversary ≤ q / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  have htable := tableBudget_from_deterministic adversary q
    (hmax.trans_lt (by norm_num)) hbound
  have hindependent := referenceBudget_from_table adversary (q - 1)
    (tableBudget_memo adversary (q - 1) htable)
  have hcomparison := forgeAdvantage_deterministic_le_reference adversary (q - 1) htable
  by_cases hone : q = 1
  · subst q
    have hbudget : HasHashQueryBound Concrete.scheme (memoAdversary adversary) 1 := by
      rw [hasHashQueryBound_iff] at hindependent ⊢
      exact hindependent.mono (by decide)
    have hsecurity : forgeAdvantage Concrete.scheme (memoAdversary adversary) ≤
        (1 : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
      simpa only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using
        Concrete.security128_below_trivial_budget 1 (by decide)
          (by norm_num) (memoAdversary adversary) hbudget
    simp only [Nat.sub_self, Nat.cast_zero, ENNReal.zero_div, add_zero] at hcomparison
    calc
      forgeAdvantage scheme adversary ≤
          forgeAdvantage Concrete.scheme (memoAdversary adversary) := hcomparison
      _ ≤ ((1 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
        simpa using hsecurity
  · have hsecurity : forgeAdvantage Concrete.scheme (memoAdversary adversary) ≤
        ((q - 1 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
      simpa only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using
        Concrete.security128_below_trivial_budget (q - 1)
          (by omega) ((Nat.sub_le q 1).trans hmax)
          (memoAdversary adversary) hindependent
    exact hcomparison.trans ((add_le_add hsecurity le_rfl).trans
      (seed_loss_absorbed128 q hq hmax))

/-- info: 'SphincsSecurity.Seeded.scheme_security128_below_trivial_final' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms scheme_security128_below_trivial_final

end SphincsSecurity.Seeded
