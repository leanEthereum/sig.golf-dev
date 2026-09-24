import SigGolfCandidate.SphincsVerifierHashSetup

/-!
# First HASH input memory invariants

The two 20-byte copies write only to the hash buffer. The four scratch words
zeroed at entry therefore remain zero when the commitment header is built.
-/

namespace SigGolfCandidate.SphincsVerifierHashMemory
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierCopy
open SigGolfCandidate.SphincsVerifierCopyMemory
open SigGolfCandidate.SphincsVerifierCopyParameter
open SigGolfCandidate.SphincsVerifierHashSetup

private theorem copy_scratch (state : MachineState) (slot : Fin 4)
    (destination : state.getReg .x7 = 0x40014 ∨ state.getReg .x7 = 0x40028) :
    (copyRootState state).getMem
      (BitVec.ofNat 64 (0x43000 + 8 * slot.val)) =
      state.getMem (BitVec.ofNat 64 (0x43000 + 8 * slot.val)) := by
  apply copyRoot_mem_frame
  intro offset
  rcases destination with destination | destination <;>
    fin_cases slot <;> fin_cases offset <;>
    simp [destination, signExtend12, alignToDword]

theorem setupAndBoth_scratch (state : MachineState) (slot : Fin 4) :
    (setupAndBothState state).getMem
      (BitVec.ofNat 64 (0x43000 + 8 * slot.val)) = 0 := by
  let jumped := execInstrBr state (.JAL .x0 16)
  let scratch := SphincsVerifierSlots.headerState jumped
  let firstPointers := addressSetupState scratch
  let firstCopy := copyRootState firstPointers
  let secondPointers := parameterPointers firstCopy
  have zero : scratch.getMem (BitVec.ofNat 64 (0x43000 + 8 * slot.val)) = 0 :=
    SphincsVerifierSlots.header_zero jumped slot
  have pointerMemory := addressSetup_memory scratch
    (BitVec.ofNat 64 (0x43000 + 8 * slot.val))
  have firstDst := (addressSetup_regs scratch).2
  have firstMemory := copy_scratch firstPointers slot (Or.inl firstDst)
  have secondPointerMemory := parameterPointers_memory firstCopy
    (BitVec.ofNat 64 (0x43000 + 8 * slot.val))
  have secondDst := (parameterPointers_regs firstCopy).2
  have secondMemory := copy_scratch secondPointers slot (Or.inr secondDst)
  exact secondMemory.trans (secondPointerMemory.trans
    (firstMemory.trans (pointerMemory.trans zero)))

theorem tag_value_after_copies (state : MachineState) :
    (SphincsVerifierHeader.tagState (setupAndBothState state)).getWord32
      0x40000 = 0xd01 := by
  have layerZero : (setupAndBothState state).getMem 0x43000 = 0 := by
    simpa using setupAndBoth_scratch state 0
  exact SphincsVerifierHeader.tag_value (setupAndBothState state) layerZero

/-- info: 'SigGolfCandidate.SphincsVerifierHashMemory.setupAndBoth_scratch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms setupAndBoth_scratch

end SigGolfCandidate.SphincsVerifierHashMemory
