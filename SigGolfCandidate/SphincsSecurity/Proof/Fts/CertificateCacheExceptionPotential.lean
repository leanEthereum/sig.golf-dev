import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Fts.CachedIndexExcessConcentration
import SigGolfCandidate.SphincsSecurity.Proof.Base.FourthMomentExceptionBound
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal

def CertificateCacheExceptional (key : SecretKey) (cache : QueryCache HashSpec) : Prop :=
  MessageDeficitExceptional key cache ∨ CachedIndexExcessExceptional key.parameter cache

noncomputable def certificateCacheExceptionPotential (key : SecretKey) (remaining : Nat)
    (cache : QueryCache HashSpec) : ENNReal :=
  fourthMomentBudget remaining (messageDeficitMoment key.parameter key.root cache 2)
      (messageDeficitMoment key.parameter key.root cache 4) / 2 ^ 364 +
    (cachedIndexExcessMoment key.parameter cache + (remaining : ENNReal) * (2 ^ 8 : ENNReal)⁻¹) / 2 ^ 148

theorem certificateCacheExceptionPotential_bad (key : SecretKey) (remaining : Nat)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (hbad : CertificateCacheExceptional key cache) :
    1 ≤ certificateCacheExceptionPotential key remaining cache := by
  rcases hbad with hdeficit | hindex
  · apply le_trans (b := fourthMomentBudget remaining (messageDeficitMoment key.parameter key.root cache 2)
      (messageDeficitMoment key.parameter key.root cache 4) / 2 ^ 364) _ le_self_add
    calc
      1 = (2 ^ 364 : ENNReal) / 2 ^ 364 := (ENNReal.div_self (by positivity) (by finiteness)).symm
      _ ≤ _ := ENNReal.div_le_div_right
        ((messageDeficitExceptional_fourthMoment_le key cache hfinite hdeficit).trans
          (fourth_le_fourthMomentBudget remaining _ _)) _
  · apply le_trans (b := (cachedIndexExcessMoment key.parameter cache +
      (remaining : ENNReal) * (2 ^ 8 : ENNReal)⁻¹) / 2 ^ 148) _ le_add_self
    calc
      1 = (2 ^ 148 : ENNReal) / 2 ^ 148 := (ENNReal.div_self (by positivity) (by finiteness)).symm
      _ ≤ _ := ENNReal.div_le_div_right
        ((cachedIndexExcessExceptional_moment_ge key.parameter cache hindex).trans le_self_add) _

theorem certificateCacheExceptionPotential_initial_le (key : SecretKey) (q : Nat) (hq : q ≤ 2 ^ 127)
    (cache : QueryCache HashSpec)
    (hnone : ∀ input, FtsProbeSimulation.MessageHashInput key.parameter input → cache input = none) :
    certificateCacheExceptionPotential key q cache ≤ (q : ENNReal) / 2 ^ 215 + (q : ENNReal) / 2 ^ 156 := by
  have hcells : ∀ payload, cache (tweakableHashInput key.parameter .message payload) = none :=
    fun payload => hnone _ ⟨payload, rfl⟩
  have hcounts := cachedMessageEntryCount_zero_of_no_inputs key.parameter key.root cache hcells
  rw [certificateCacheExceptionPotential,
    messageDeficitMoment_zero_of_no_inputs key.parameter key.root cache hcounts 2 (by decide),
    messageDeficitMoment_zero_of_no_inputs key.parameter key.root cache hcounts 4 (by decide),
    cachedIndexExcessMoment_zero_of_no_message key.parameter cache hnone, zero_add]
  apply add_le_add (fourthMomentBudget_zero_le q hq)
  apply le_of_eq
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_inv]
  ring

end SphincsSecurity.Concrete
