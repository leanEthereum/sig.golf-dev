import SigGolfCandidate.SphincsSecurity.Proof.Adversary.Security
import SigGolfCandidate.SphincsSecurity.Proof.Deterministic.Security128

open OracleComp OracleSpec ENNReal

namespace SphincsSecurity.Security

set_option backward.isDefEq.respectTransparency false

/-- The actual deterministic-seed adversary game has an internal 128-bit bound throughout the range relevant to a final 127-bit claim. -/
theorem security128_below_trivial_final (q : Nat) (hq : 1 ≤ q)
    (hmax : q ≤ 2 ^ 127) (adversary : Adversary)
    (hbound : HasHashQueryBound adversary q) :
    forgeAdvantage adversary ≤ q / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  rw [← advantage_embed]
  apply Seeded.scheme_security128_below_trivial_final q hq hmax
  change ∀ result ∈ support ((simulateQ countedRomImpl
    (SphincsSecurity.gameCore Seeded.scheme (embed adversary))).run.run' ∅), result.2 ≤ q
  rw [experiment_embed]
  exact hbound

/-- info: 'SphincsSecurity.Security.security128_below_trivial_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms security128_below_trivial_final

end SphincsSecurity.Security
