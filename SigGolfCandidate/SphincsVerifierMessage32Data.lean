import SigGolfCandidate.SphincsVerifierMessage32

/-!
# Message copy contents

The four exact verifier loop iterations leave the four 64-bit input message
words in the next HASH buffer and preserve the original message.
-/

namespace SigGolfCandidate.SphincsVerifierMessage32Data
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierMessage32
open SigGolfCandidate.Sphincs.Expansion

private def sourceWord (index : Nat) : Word :=
  BitVec.ofNat 64 (8 * index)

private def destinationWord (index : Nat) : Word :=
  BitVec.ofNat 64 (0x40050 + 8 * index)

private theorem destination_injective (left right : Nat)
    (hl : left < 4) (hr : right < 4)
    (equal : destinationWord left = destinationWord right) : left = right := by
  have bits := congrArg BitVec.toNat equal
  simp only [destinationWord, BitVec.toNat_ofNat] at bits
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at bits
  omega

private theorem source_ne_destination (source destination : Nat)
    (hs : source < 4) (hd : destination < 4) :
    sourceWord source ≠ destinationWord destination := by
  intro equal
  have bits := congrArg BitVec.toNat equal
  simp only [sourceWord, destinationWord, BitVec.toNat_ofNat] at bits
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at bits
  omega

def CopyData (original : MachineState) (copied : Nat)
    (state : MachineState) : Prop :=
  (∀ index : Fin 4, index.val < copied →
    state.getMem (destinationWord index.val) =
      original.getMem (sourceWord index.val)) ∧
  (∀ index : Fin 4,
    state.getMem (sourceWord index.val) =
      original.getMem (sourceWord index.val))

theorem copyData_initial (state : MachineState) : CopyData state 0 state := by
  constructor
  · intro index impossible
    omega
  · intro index
    rfl

theorem copyData_step (original state : MachineState) (remaining : Nat)
    (inv : LoopInvariant (remaining + 1) state)
    (data : CopyData original (4 - (remaining + 1)) state) :
    CopyData original (4 - remaining) (loopNext state) := by
  obtain ⟨bound, _, source, destination, _⟩ := inv
  have doneBound : 4 - (remaining + 1) < 4 := by omega
  have nextDone : 4 - remaining = 4 - (remaining + 1) + 1 := by omega
  constructor
  · intro index copied
    rw [loop_next_mem]
    rw [destination]
    change (if destinationWord index.val =
        destinationWord (4 - (remaining + 1)) then
          state.getMem (state.getReg .x6)
        else state.getMem (destinationWord index.val)) =
      original.getMem (sourceWord index.val)
    by_cases same : index.val = 4 - (remaining + 1)
    · have address : destinationWord index.val =
          destinationWord (4 - (remaining + 1)) := by rw [same]
      rw [address, if_pos rfl, source]
      simpa [sourceWord, same] using data.2 index
    · have other : destinationWord index.val ≠
          destinationWord (4 - (remaining + 1)) := by
        intro equal
        exact same (destination_injective _ _ index.isLt doneBound equal)
      rw [if_neg other]
      exact data.1 index (by omega)
  · intro index
    rw [loop_next_mem]
    rw [destination]
    change (if sourceWord index.val =
        destinationWord (4 - (remaining + 1)) then
          state.getMem (state.getReg .x6)
        else state.getMem (sourceWord index.val)) =
      original.getMem (sourceWord index.val)
    have other := source_ne_destination index.val
      (4 - (remaining + 1)) index.isLt doneBound
    rw [if_neg other]
    exact data.2 index

/-- info: 'SigGolfCandidate.SphincsVerifierMessage32Data.copyData_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms copyData_step

end SigGolfCandidate.SphincsVerifierMessage32Data
