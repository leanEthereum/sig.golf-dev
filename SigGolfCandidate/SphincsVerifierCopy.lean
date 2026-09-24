import SigGolfCandidate.SphincsVerifierSlots

/-!
# Verifier commitment input pointers

The four instructions after scratch initialization set the source pointer to
the witness and the destination pointer to the commitment's root field.
-/

namespace SigGolfCandidate.SphincsVerifierCopy
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierPrefix

def addressSetupState (state : MachineState) : MachineState :=
  let state := execInstrBr state (.LUI .x6 0x23)
  let state := execInstrBr state (.ADDI .x6 .x6 (-864))
  let state := execInstrBr state (.LUI .x7 0x40)
  execInstrBr state (.ADDI .x7 .x7 20)

theorem addressSetup_block (state : MachineState) (pc : state.pc = 0x1050) :
    OrdinarySteps SphincsImages.verify state 4 (addressSetupState state) := by
  let s1 := execInstrBr state (.LUI .x6 0x23)
  let s2 := execInstrBr s1 (.ADDI .x6 .x6 (-864))
  let s3 := execInstrBr s2 (.LUI .x7 0x40)
  let s4 := execInstrBr s3 (.ADDI .x7 .x7 20)
  apply OrdinarySteps.step state s1 _ (.base (.LUI .x6 0x23)) 3
  · rw [fetch_at state 20 (by decide) (by simpa using pc)]
    decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x6 .x6 (-864))) 2
  · have hp : s1.pc = 0x1054 := by simp [s1, execInstrBr, MachineState.setPC, pc]
    rw [fetch_at s1 21 (by decide) (by simpa using hp)]
    decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LUI .x7 0x40)) 1
  · have hp : s2.pc = 0x1058 := by simp [s1, s2, execInstrBr, MachineState.setPC, pc]
    rw [fetch_at s2 22 (by decide) (by simpa using hp)]
    decide
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x7 .x7 20)) 0
  · have hp : s3.pc = 0x105c := by
      simp [s1, s2, s3, execInstrBr, MachineState.setPC, pc]
    rw [fetch_at s3 23 (by decide) (by simpa using hp)]
    decide
  · rfl
  exact OrdinarySteps.refl _

theorem addressSetup_pc (state : MachineState) (pc : state.pc = 0x1050) :
    (addressSetupState state).pc = 0x1060 := by
  simp [addressSetupState, execInstrBr, MachineState.setPC, pc]

theorem addressSetup_regs (state : MachineState) :
    (addressSetupState state).getReg .x6 = 0x22ca0 ∧
      (addressSetupState state).getReg .x7 = 0x40014 := by
  simp [addressSetupState, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.getReg_setPC]

theorem addressSetup_memory (state : MachineState) (address : Word) :
    (addressSetupState state).getMem address = state.getMem address := by
  simp [addressSetupState, execInstrBr]

def copyWordState (offset : Fin 5) (state : MachineState) : MachineState :=
  execInstrBr (execInstrBr state (.LWU .x13 .x6 (4 * offset.val)))
    (.SW .x7 .x13 (4 * offset.val))

private theorem getReg_setWord32 (state : MachineState) (address : Word)
    (value : BitVec 32) (register : Reg) :
    (state.setWord32 address value).getReg register = state.getReg register := rfl

theorem copyWord_block (offset : Fin 5) (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (0x1060 + 8 * offset.val))
    (source : state.getReg .x6 = 0x22ca0)
    (destination : state.getReg .x7 = 0x40014) :
    OrdinarySteps SphincsImages.verify state 2 (copyWordState offset state) := by
  let loaded := execInstrBr state (.LWU .x13 .x6 (4 * offset.val))
  let copied := execInstrBr loaded (.SW .x7 .x13 (4 * offset.val))
  have hp0 : state.pc = BitVec.ofNat 64 (0x1000 + 4 * (24 + 2 * offset.val)) := by
    rw [pc]
    congr 1
    omega
  have hp1 : loaded.pc = BitVec.ofNat 64 (0x1000 + 4 * (25 + 2 * offset.val)) := by
    fin_cases offset <;>
      simp [loaded, execInstrBr, MachineState.setPC, pc]
  apply OrdinarySteps.step state loaded _ (.base (.LWU .x13 .x6 (4 * offset.val))) 1
  · rw [fetch_at state (24 + 2 * offset.val) (by omega) hp0]
    fin_cases offset <;> decide
  · have hvalid : memoryArgumentsValid state (.LWU .x13 .x6 (4 * offset.val)) = true := by
      fin_cases offset <;>
        simp [memoryArgumentsValid, accessValid, rangeValid,
          signExtend12, source, MEMORY_BYTES]
    fin_cases offset <;>
      simp [loaded, ordinaryStep, memoryArgumentsValid, accessValid,
        rangeValid, signExtend12, source, MEMORY_BYTES]
  apply OrdinarySteps.step loaded copied _ (.base (.SW .x7 .x13 (4 * offset.val))) 0
  · rw [fetch_at loaded (25 + 2 * offset.val) (by omega) hp1]
    fin_cases offset <;> decide
  · have hdst : loaded.getReg .x7 = 0x40014 := by
      simp [loaded, execInstrBr, MachineState.getReg_setReg_ne, destination]
    have hvalid : memoryArgumentsValid loaded (.SW .x7 .x13 (4 * offset.val)) = true := by
      fin_cases offset <;>
        simp [memoryArgumentsValid, accessValid, rangeValid,
          signExtend12, hdst, MEMORY_BYTES]
    fin_cases offset <;>
      simp [copied, ordinaryStep, memoryArgumentsValid, accessValid,
        rangeValid, signExtend12, hdst, MEMORY_BYTES]
  exact OrdinarySteps.refl _

theorem copyWord_pc (offset : Fin 5) (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (0x1060 + 8 * offset.val)) :
    (copyWordState offset state).pc = BitVec.ofNat 64 (0x1068 + 8 * offset.val) := by
  fin_cases offset <;>
    simp [copyWordState, execInstrBr, MachineState.setPC, pc]

theorem copyWord_pointers (offset : Fin 5) (state : MachineState) :
    (copyWordState offset state).getReg .x6 = state.getReg .x6 ∧
      (copyWordState offset state).getReg .x7 = state.getReg .x7 := by
  simp [copyWordState, execInstrBr, getReg_setWord32,
    MachineState.getReg_setReg_ne]

def copyRootState (state : MachineState) : MachineState :=
  copyWordState 4 (copyWordState 3 (copyWordState 2
    (copyWordState 1 (copyWordState 0 state))))

theorem copyRoot_block (state : MachineState) (pc : state.pc = 0x1060)
    (source : state.getReg .x6 = 0x22ca0)
    (destination : state.getReg .x7 = 0x40014) :
    OrdinarySteps SphincsImages.verify state 10 (copyRootState state) := by
  let s1 := copyWordState 0 state
  let s2 := copyWordState 1 s1
  let s3 := copyWordState 2 s2
  let s4 := copyWordState 3 s3
  let s5 := copyWordState 4 s4
  have b0 : OrdinarySteps SphincsImages.verify state 2 s1 :=
    copyWord_block 0 state (by simpa using pc) source destination
  have p1 : s1.pc = 0x1068 := copyWord_pc 0 state (by simpa using pc)
  have src1 : s1.getReg .x6 = 0x22ca0 := (copyWord_pointers 0 state).1.trans source
  have dst1 : s1.getReg .x7 = 0x40014 := (copyWord_pointers 0 state).2.trans destination
  have b1 : OrdinarySteps SphincsImages.verify s1 2 s2 :=
    copyWord_block 1 s1 (by simpa using p1) src1 dst1
  have p2 : s2.pc = 0x1070 := copyWord_pc 1 s1 (by simpa using p1)
  have src2 : s2.getReg .x6 = 0x22ca0 := (copyWord_pointers 1 s1).1.trans src1
  have dst2 : s2.getReg .x7 = 0x40014 := (copyWord_pointers 1 s1).2.trans dst1
  have b2 : OrdinarySteps SphincsImages.verify s2 2 s3 :=
    copyWord_block 2 s2 (by simpa using p2) src2 dst2
  have p3 : s3.pc = 0x1078 := copyWord_pc 2 s2 (by simpa using p2)
  have src3 : s3.getReg .x6 = 0x22ca0 := (copyWord_pointers 2 s2).1.trans src2
  have dst3 : s3.getReg .x7 = 0x40014 := (copyWord_pointers 2 s2).2.trans dst2
  have b3 : OrdinarySteps SphincsImages.verify s3 2 s4 :=
    copyWord_block 3 s3 (by simpa using p3) src3 dst3
  have p4 : s4.pc = 0x1080 := copyWord_pc 3 s3 (by simpa using p3)
  have src4 : s4.getReg .x6 = 0x22ca0 := (copyWord_pointers 3 s3).1.trans src3
  have dst4 : s4.getReg .x7 = 0x40014 := (copyWord_pointers 3 s3).2.trans dst3
  have b4 : OrdinarySteps SphincsImages.verify s4 2 s5 :=
    copyWord_block 4 s4 (by simpa using p4) src4 dst4
  simpa [copyRootState, s1, s2, s3, s4, s5] using
    (((b0.append b1).append b2).append b3).append b4

def setupAndRootState (state : MachineState) : MachineState :=
  copyRootState (addressSetupState
    (SphincsVerifierSlots.headerState (execInstrBr state (.JAL .x0 16))))

/-- The exact verifier reaches the end of the first 20-byte witness copy. -/
theorem setupAndRoot_block (state : MachineState) (pc : state.pc = 0x1000) :
    OrdinarySteps SphincsImages.verify state 31 (setupAndRootState state) := by
  let afterJump := execInstrBr state (.JAL .x0 16)
  let afterHeader := SphincsVerifierSlots.headerState afterJump
  let afterPointers := addressSetupState afterHeader
  have entry := SphincsVerifierSlots.entry_header_block state pc
  have jumpPc := SphincsVerifierCommitment.entry_next_pc state pc
  have headerPc := SphincsVerifierSlots.header_next_pc afterJump jumpPc
  have pointers := addressSetup_block afterHeader headerPc
  have pointerPc := addressSetup_pc afterHeader headerPc
  have pointerRegs := addressSetup_regs afterHeader
  have copied := copyRoot_block afterPointers pointerPc pointerRegs.1 pointerRegs.2
  simpa [setupAndRootState, afterJump, afterHeader, afterPointers] using
    (entry.append pointers).append copied

/-- info: 'SigGolfCandidate.SphincsVerifierCopy.setupAndRoot_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms setupAndRoot_block

/-- info: 'SigGolfCandidate.SphincsVerifierCopy.addressSetup_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms addressSetup_block

end SigGolfCandidate.SphincsVerifierCopy
