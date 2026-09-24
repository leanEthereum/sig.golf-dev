import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Ots.EncodingCharge
import SigGolfCandidate.SphincsSecurity.Proof.Ots.EncodingProbability
/-!
# Cache-derived encoding selection risk

The abstract conditional-selection schedule is instantiated with the concrete encoding inputs at
one structural position and one settled layer message. Every cached candidate retains its full hash
input as the identifier used to exclude the selected input itself.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

set_option maxRecDepth 100000

def encodingRetryInput (parameter : PublicParameter) (position : EncodingPosition)
    (message : Digest) (counter : Nat) : HashInput :=
  tweakableHashInput parameter position.domain
    (digestBytes message ++ counterBytes (BitVec.ofNat counterBits counter))

theorem encodingRetryInput_injective_of_lt
    {parameter : PublicParameter} {position : EncodingPosition} {message : Digest}
    {left right : Nat} (hleft : left < encodingAttemptLimit)
    (hright : right < encodingAttemptLimit)
    (heq : encodingRetryInput parameter position message left =
      encodingRetryInput parameter position message right) :
    left = right := by
  have hpayload :=
    (tweakableHashInput_injective parameter (by trivial) (by trivial) heq).2
  obtain ⟨_, hcounter⟩ :=
    List.append_inj hpayload (by simp [digestBytes_length])
  have hleft19 : left < 2 ^ counterBits :=
    lt_of_lt_of_le hleft (by decide : encodingAttemptLimit ≤ 2 ^ counterBits)
  have hright19 : right < 2 ^ counterBits :=
    lt_of_lt_of_le hright (by decide : encodingAttemptLimit ≤ 2 ^ counterBits)
  have hleft32 : left < 2 ^ 32 := lt_of_lt_of_le hleft19 (by decide)
  have hright32 : right < 2 ^ 32 := lt_of_lt_of_le hright19 (by decide)
  have hv := congrArg BitVec.toNat (bytesLE_injective hcounter)
  simp only [counterBytes, BitVec.toNat_ofNat] at hv
  norm_num [counterBits] at hleft19 hright19 hleft32 hright32 hv
  omega
