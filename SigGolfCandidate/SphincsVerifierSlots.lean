import SigGolfCandidate.SphincsVerifierPrefix

/-!
# Four commitment-header scratch slots

The first sixteen instructions after the entry jump zero the layer, tree,
position, and index scratch words. Each four-instruction block is checked
against the exact generated image.
-/

namespace SigGolfCandidate.SphincsVerifierSlots
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierPrefix

private def slotBeforeStore (slot : Fin 4) (state : MachineState) : MachineState :=
  let state := execInstrBr state (.ADDI .x6 .x0 0)
  let state := execInstrBr state (.LUI .x28 0x43)
  execInstrBr state (.ADDI .x28 .x28 (8 * slot.val))

def slotState (slot : Fin 4) (state : MachineState) : MachineState :=
  execInstrBr (slotBeforeStore slot state) (.SD .x28 .x6 0)

theorem slotBeforeStore_regs (slot : Fin 4) (state : MachineState) :
    (slotBeforeStore slot state).getReg .x28 =
      BitVec.ofNat 64 (0x43000 + 8 * slot.val) ∧
      (slotBeforeStore slot state).getReg .x6 = 0 := by
  fin_cases slot <;>
    simp [slotBeforeStore, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      MachineState.getReg_setPC]

theorem slot_next_pc (slot : Fin 4) (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (0x1010 + 16 * slot.val)) :
    (slotState slot state).pc = BitVec.ofNat 64 (0x1020 + 16 * slot.val) := by
  fin_cases slot <;>
    simp [slotState, slotBeforeStore, execInstrBr, MachineState.setPC, pc]

theorem slot_value (slot : Fin 4) (state : MachineState) :
    (slotState slot state).getMem (BitVec.ofNat 64 (0x43000 + 8 * slot.val)) = 0 := by
  obtain ⟨haddr, hvalue⟩ := slotBeforeStore_regs slot state
  simp [slotState, execInstrBr, signExtend12, haddr, hvalue]

private theorem slotBeforeStore_memory (slot : Fin 4) (state : MachineState)
    (address : Word) :
    (slotBeforeStore slot state).getMem address = state.getMem address := by
  simp [slotBeforeStore, execInstrBr]

theorem slot_memory (slot : Fin 4) (state : MachineState) (address : Word) :
    (slotState slot state).getMem address =
      if address = BitVec.ofNat 64 (0x43000 + 8 * slot.val) then 0
      else state.getMem address := by
  obtain ⟨haddr, hvalue⟩ := slotBeforeStore_regs slot state
  have hmem : (slotBeforeStore slot state).mem address = state.mem address := by
    simpa only [MachineState.getMem] using slotBeforeStore_memory slot state address
  simp only [slotState, execInstrBr, MachineState.getMem_setPC,
    signExtend12, haddr, hvalue]
  simp [MachineState.setMem, MachineState.getMem, hmem]

theorem slot_block (slot : Fin 4) (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (0x1010 + 16 * slot.val)) :
    OrdinarySteps SphincsImages.verify state 4 (slotState slot state) := by
  let s1 := execInstrBr state (.ADDI .x6 .x0 0)
  let s2 := execInstrBr s1 (.LUI .x28 0x43)
  let s3 := execInstrBr s2 (.ADDI .x28 .x28 (8 * slot.val))
  let s4 := execInstrBr s3 (.SD .x28 .x6 0)
  have hp0 : state.pc = BitVec.ofNat 64 (0x1000 + 4 * (4 + 4 * slot.val)) := by
    rw [pc]
    congr 1
    omega
  have hp1 : s1.pc = BitVec.ofNat 64 (0x1000 + 4 * (5 + 4 * slot.val)) := by
    fin_cases slot <;>
      simp [s1, execInstrBr, MachineState.setPC, pc]
  have hp2 : s2.pc = BitVec.ofNat 64 (0x1000 + 4 * (6 + 4 * slot.val)) := by
    fin_cases slot <;>
      simp [s1, s2, execInstrBr, MachineState.setPC, pc]
  have hp3 : s3.pc = BitVec.ofNat 64 (0x1000 + 4 * (7 + 4 * slot.val)) := by
    fin_cases slot <;>
      simp [s1, s2, s3, execInstrBr, MachineState.setPC, pc]
  apply OrdinarySteps.step state s1 _ (.base (.ADDI .x6 .x0 0)) 3
  · rw [fetch_at state (4 + 4 * slot.val) (by omega) hp0]
    fin_cases slot <;> decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x28 0x43)) 2
  · rw [fetch_at s1 (5 + 4 * slot.val) (by omega) hp1]
    fin_cases slot <;> decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x28 .x28 (8 * slot.val))) 1
  · rw [fetch_at s2 (6 + 4 * slot.val) (by omega) hp2]
    fin_cases slot <;> decide
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.SD .x28 .x6 0)) 0
  · rw [fetch_at s3 (7 + 4 * slot.val) (by omega) hp3]
    fin_cases slot <;> decide
  · have haddr : s3.getReg .x28 =
        BitVec.ofNat 64 (0x43000 + 8 * slot.val) := by
      simpa only [s3, s2, s1, slotBeforeStore] using
        (slotBeforeStore_regs slot state).1
    have hvalid : memoryArgumentsValid s3 (.SD .x28 .x6 0) = true := by
      fin_cases slot <;>
        simp [memoryArgumentsValid, accessValid, rangeValid,
          signExtend12, haddr, MEMORY_BYTES]
    simp only [ordinaryStep, hvalid, ite_true, s4]
  exact OrdinarySteps.refl _

def headerState (state : MachineState) : MachineState :=
  slotState 3 (slotState 2 (slotState 1 (slotState 0 state)))

theorem header_block (state : MachineState) (pc : state.pc = 0x1010) :
    OrdinarySteps SphincsImages.verify state 16 (headerState state) := by
  let s1 := slotState 0 state
  let s2 := slotState 1 s1
  let s3 := slotState 2 s2
  let s4 := slotState 3 s3
  have b0 : OrdinarySteps SphincsImages.verify state 4 s1 :=
    slot_block 0 state (by simpa using pc)
  have p1 : s1.pc = 0x1020 := slot_next_pc 0 state (by simpa using pc)
  have b1 : OrdinarySteps SphincsImages.verify s1 4 s2 :=
    slot_block 1 s1 (by simpa using p1)
  have p2 : s2.pc = 0x1030 := slot_next_pc 1 s1 (by simpa using p1)
  have b2 : OrdinarySteps SphincsImages.verify s2 4 s3 :=
    slot_block 2 s2 (by simpa using p2)
  have p3 : s3.pc = 0x1040 := slot_next_pc 2 s2 (by simpa using p2)
  have b3 : OrdinarySteps SphincsImages.verify s3 4 s4 :=
    slot_block 3 s3 (by simpa using p3)
  simpa [headerState, s1, s2, s3, s4] using
    ((b0.append b1).append b2).append b3

theorem header_next_pc (state : MachineState) (pc : state.pc = 0x1010) :
    (headerState state).pc = 0x1050 := by
  have p1 := slot_next_pc 0 state (by simpa using pc)
  have p2 := slot_next_pc 1 (slotState 0 state) (by simpa using p1)
  have p3 := slot_next_pc 2 (slotState 1 (slotState 0 state)) (by simpa using p2)
  have p4 := slot_next_pc 3 (slotState 2 (slotState 1 (slotState 0 state)))
    (by simpa using p3)
  simpa [headerState] using p4

theorem header_zero (state : MachineState) (slot : Fin 4) :
    (headerState state).getMem (BitVec.ofNat 64 (0x43000 + 8 * slot.val)) = 0 := by
  fin_cases slot <;>
    simp [headerState, slot_memory]

/-- Entry plus the four scratch writes: 17 certified ordinary instructions. -/
theorem entry_header_block (state : MachineState) (pc : state.pc = 0x1000) :
    OrdinarySteps SphincsImages.verify state 17
      (headerState (execInstrBr state (.JAL .x0 16))) := by
  have entry := SphincsVerifierCommitment.entry_block state pc
  have nextPc := SphincsVerifierCommitment.entry_next_pc state pc
  have header := header_block (execInstrBr state (.JAL .x0 16)) nextPc
  simpa using entry.append header

/-- info: 'SigGolfCandidate.SphincsVerifierSlots.entry_header_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms entry_header_block

end SigGolfCandidate.SphincsVerifierSlots
