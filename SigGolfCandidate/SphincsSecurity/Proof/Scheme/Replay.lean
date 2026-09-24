import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Ots.EncodingCached
import SigGolfCandidate.SphincsSecurity.Proof.Scheme.ForgeryClassify
/-!
# Replay and message-digest collisions

If one signing entry has the forgery's complete admissible digest, a fully honest opening is the
returned signature unless the two distinct message-digest inputs have the same answer.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

theorem messageDigestPayload_injective (root : Digest) {leftMessage rightMessage : Message}
    {leftRandomness rightRandomness : Randomness}
    (h : messageDigestPayload root leftMessage leftRandomness
      = messageDigestPayload root rightMessage rightRandomness) :
    leftMessage = rightMessage ∧ leftRandomness = rightRandomness := by
  simp only [messageDigestPayload] at h
  obtain ⟨hrandomness, hrest⟩ := List.append_inj h (by
    simp only [List.length_append]
    rw [bytesLE_length 20 leftRandomness, bytesLE_length 20 rightRandomness])
  have hrandomness' := List.append_cancel_right hrandomness
  exact ⟨bytesLE_injective hrest, bytesLE_injective hrandomness'⟩

end SphincsSecurity.Concrete
