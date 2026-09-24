import SigGolfCandidate.SphincsWire
import SigGolfCandidate.SphincsSecurity.Proof.Scheme.Bytes
import SigGolfCandidate.Hypertree.SecurityUniform

/-!
# Public-key commitment encoding

The 16-byte beta public key commits to the internal root and public parameter.
Its oracle input has a unique encoding and a tag outside every hash domain
used by the internal scheme, including key derivation and nonce generation.
-/

namespace SigGolfCandidate.SphincsWire
open SphincsSecurity
open OracleComp OracleSpec

private theorem commitment_tweak_length :
    (fieldBytes (tweakFields 13 0 0 0 0)).length = 20 := by
  simp [fieldBytes, bytesLE_length]

/-- A commitment query names one and only one internal public key. -/
theorem commitmentInput_injective : Function.Injective commitmentInput := by
  intro left right h
  unfold commitmentInput at h
  simp only [List.append_assoc] at h
  obtain ⟨_, htail⟩ := List.append_inj h (by simp [commitment_tweak_length])
  have hlen : (bytesLE digestBytes left.root).length =
      (bytesLE digestBytes right.root).length := by
    simp [bytesLE]
  obtain ⟨hroot, hparameter⟩ := List.append_inj htail hlen
  cases left
  cases right
  simp only [PublicKey.mk.injEq]
  exact ⟨bytesLE_injective hroot, bytesLE_injective hparameter⟩

/-- Commitment queries cannot coincide with any ordinary verification hash query. -/
theorem commitmentInput_ne_tweakableHashInput (publicKey : PublicKey)
    (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    commitmentInput publicKey ≠ tweakableHashInput parameter domain payload := by
  intro h
  unfold commitmentInput tweakableHashInput tweakBytes at h
  simp only [digestBytes, List.append_assoc] at h
  obtain ⟨htweak, _⟩ := List.append_inj h
    (by simp [fieldBytes, bytesLE_length])
  have htag := congrArg TweakFields.tag (fieldBytes_injective htweak)
  cases domain <;> simp [hashDomainFields, tweakFields] at htag

/-- Commitment queries cannot coincide with key-derivation queries. -/
theorem commitmentInput_ne_keygenHashInput (publicKey : PublicKey)
    (parameter : PublicParameter) (domain : KeygenDomain) (seed : MasterSeed) :
    commitmentInput publicKey ≠ keygenHashInput parameter domain seed := by
  intro h
  unfold commitmentInput keygenHashInput at h
  simp only [digestBytes, List.append_assoc] at h
  obtain ⟨htweak, _⟩ := List.append_inj h
    (by simp [fieldBytes, bytesLE_length])
  have htag := congrArg TweakFields.tag (fieldBytes_injective htweak)
  cases domain <;> simp [keygenDomainFields, tweakFields] at htag

/-- Commitment queries cannot coincide with nonce-generation queries. -/
theorem commitmentInput_ne_randomizerHashInput (publicKey : PublicKey)
    (parameter : PublicParameter) (seed : MasterSeed) (message : Message)
    (trial : BitVec 32) :
    commitmentInput publicKey ≠ randomizerHashInput parameter seed message trial := by
  intro h
  unfold commitmentInput randomizerHashInput at h
  simp only [digestBytes, List.append_assoc] at h
  obtain ⟨htweak, _⟩ := List.append_inj h
    (by simp [fieldBytes, bytesLE_length])
  have htag := congrArg TweakFields.tag (fieldBytes_injective htweak)
  simp [tweakFields] at htag

/-- One fresh commitment response hits a fixed 16-byte public key with probability `2^-128`. -/
theorem commitment_guess_probability (target : BitVec 128) :
    Pr[fun output : HashOutput => output.extractLsb' 0 128 = target |
      ($ᵗ HashOutput)] = 1 / 2 ^ (128 : Nat) := by
  change Pr[fun output : BitVec (128 + 128) => output.extractLsb' 0 128 = target |
    ($ᵗ BitVec (128 + 128))] = 1 / 2 ^ (128 : Nat)
  simpa only [Finset.mem_singleton, Finset.card_singleton, Nat.cast_one] using
    SigGolfCandidate.Hypertree.SecurityUniform.prob_extract_mem 128 128
      ({target} : Finset (BitVec 128))

/-- info: 'SigGolfCandidate.SphincsWire.commitmentInput_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms commitmentInput_injective

/-- info: 'SigGolfCandidate.SphincsWire.commitment_guess_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms commitment_guess_probability

end SigGolfCandidate.SphincsWire
