import SigGolfCandidate.SphincsVerifierCopyMemory

/-!
# Verifier parameter copy

The second five-word copy moves the public parameter from the witness to the
commitment hash buffer. The same load/store semantics used for the root apply.
-/

namespace SigGolfCandidate.SphincsVerifierCopyParameter
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierPrefix
open SigGolfCandidate.SphincsVerifierCopy

def parameterPointers (state : MachineState) : MachineState :=
  let state := execInstrBr state (.LUI .x6 0x23)
  let state := execInstrBr state (.ADDI .x6 .x6 (-844))
  let state := execInstrBr state (.LUI .x7 0x40)
  execInstrBr state (.ADDI .x7 .x7 40)

theorem parameterPointers_block (state : MachineState) (pc : state.pc = 0x1088) :
    OrdinarySteps SphincsImages.verify state 4 (parameterPointers state) := by
  let s1 := execInstrBr state (.LUI .x6 0x23)
  let s2 := execInstrBr s1 (.ADDI .x6 .x6 (-844))
  let s3 := execInstrBr s2 (.LUI .x7 0x40)
  let s4 := execInstrBr s3 (.ADDI .x7 .x7 40)
  apply OrdinarySteps.step state s1 _ (.base (.LUI .x6 0x23)) 3
  · rw [fetch_at state 34 (by decide) (by simpa using pc)]
    decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x6 .x6 (-844))) 2
  · have hp : s1.pc = 0x108c := by simp [s1, execInstrBr, MachineState.setPC, pc]
    rw [fetch_at s1 35 (by decide) (by simpa using hp)]
    decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LUI .x7 0x40)) 1
  · have hp : s2.pc = 0x1090 := by simp [s1, s2, execInstrBr, MachineState.setPC, pc]
    rw [fetch_at s2 36 (by decide) (by simpa using hp)]
    decide
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x7 .x7 40)) 0
  · have hp : s3.pc = 0x1094 := by
      simp [s1, s2, s3, execInstrBr, MachineState.setPC, pc]
    rw [fetch_at s3 37 (by decide) (by simpa using hp)]
    decide
  · rfl
  exact OrdinarySteps.refl _

theorem parameterPointers_pc (state : MachineState) (pc : state.pc = 0x1088) :
    (parameterPointers state).pc = 0x1098 := by
  simp [parameterPointers, execInstrBr, MachineState.setPC, pc]

theorem parameterPointers_regs (state : MachineState) :
    (parameterPointers state).getReg .x6 = 0x22cb4 ∧
      (parameterPointers state).getReg .x7 = 0x40028 := by
  simp [parameterPointers, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.getReg_setPC]

theorem parameterPointers_memory (state : MachineState) (address : Word) :
    (parameterPointers state).getMem address = state.getMem address := by
  simp [parameterPointers, execInstrBr]

theorem copyParameterWord_block (offset : Fin 5) (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (0x1098 + 8 * offset.val))
    (source : state.getReg .x6 = 0x22cb4)
    (destination : state.getReg .x7 = 0x40028) :
    OrdinarySteps SphincsImages.verify state 2 (copyWordState offset state) := by
  let loaded := execInstrBr state (.LWU .x13 .x6 (4 * offset.val))
  let copied := execInstrBr loaded (.SW .x7 .x13 (4 * offset.val))
  have hp0 : state.pc = BitVec.ofNat 64 (0x1000 + 4 * (38 + 2 * offset.val)) := by
    rw [pc]
    congr 1
    omega
  have hp1 : loaded.pc = BitVec.ofNat 64 (0x1000 + 4 * (39 + 2 * offset.val)) := by
    fin_cases offset <;>
      simp [loaded, execInstrBr, MachineState.setPC, pc]
  apply OrdinarySteps.step state loaded _ (.base (.LWU .x13 .x6 (4 * offset.val))) 1
  · rw [fetch_at state (38 + 2 * offset.val) (by omega) hp0]
    fin_cases offset <;> decide
  · fin_cases offset <;>
      simp [loaded, ordinaryStep, memoryArgumentsValid, accessValid,
        rangeValid, signExtend12, source, MEMORY_BYTES]
  apply OrdinarySteps.step loaded copied _ (.base (.SW .x7 .x13 (4 * offset.val))) 0
  · rw [fetch_at loaded (39 + 2 * offset.val) (by omega) hp1]
    fin_cases offset <;> decide
  · have hdst : loaded.getReg .x7 = 0x40028 := by
      simp [loaded, execInstrBr, MachineState.getReg_setReg_ne, destination]
    fin_cases offset <;>
      simp [copied, ordinaryStep, memoryArgumentsValid, accessValid,
        rangeValid, signExtend12, hdst, MEMORY_BYTES]
  exact OrdinarySteps.refl _

theorem copyParameterWord_pc (offset : Fin 5) (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (0x1098 + 8 * offset.val)) :
    (copyWordState offset state).pc = BitVec.ofNat 64 (0x10a0 + 8 * offset.val) := by
  fin_cases offset <;>
    simp [copyWordState, execInstrBr, MachineState.setPC, pc]

theorem copyParameter_block (state : MachineState) (pc : state.pc = 0x1098)
    (source : state.getReg .x6 = 0x22cb4)
    (destination : state.getReg .x7 = 0x40028) :
    OrdinarySteps SphincsImages.verify state 10 (copyRootState state) := by
  let s1 := copyWordState 0 state
  let s2 := copyWordState 1 s1
  let s3 := copyWordState 2 s2
  let s4 := copyWordState 3 s3
  let s5 := copyWordState 4 s4
  have b0 := copyParameterWord_block 0 state (by simpa using pc) source destination
  have p1 : s1.pc = 0x10a0 := copyParameterWord_pc 0 state (by simpa using pc)
  have src1 : s1.getReg .x6 = 0x22cb4 := (copyWord_pointers 0 state).1.trans source
  have dst1 : s1.getReg .x7 = 0x40028 := (copyWord_pointers 0 state).2.trans destination
  have b1 := copyParameterWord_block 1 s1 (by simpa using p1) src1 dst1
  have p2 : s2.pc = 0x10a8 := copyParameterWord_pc 1 s1 (by simpa using p1)
  have src2 : s2.getReg .x6 = 0x22cb4 := (copyWord_pointers 1 s1).1.trans src1
  have dst2 : s2.getReg .x7 = 0x40028 := (copyWord_pointers 1 s1).2.trans dst1
  have b2 := copyParameterWord_block 2 s2 (by simpa using p2) src2 dst2
  have p3 : s3.pc = 0x10b0 := copyParameterWord_pc 2 s2 (by simpa using p2)
  have src3 : s3.getReg .x6 = 0x22cb4 := (copyWord_pointers 2 s2).1.trans src2
  have dst3 : s3.getReg .x7 = 0x40028 := (copyWord_pointers 2 s2).2.trans dst2
  have b3 := copyParameterWord_block 3 s3 (by simpa using p3) src3 dst3
  have p4 : s4.pc = 0x10b8 := copyParameterWord_pc 3 s3 (by simpa using p3)
  have src4 : s4.getReg .x6 = 0x22cb4 := (copyWord_pointers 3 s3).1.trans src3
  have dst4 : s4.getReg .x7 = 0x40028 := (copyWord_pointers 3 s3).2.trans dst3
  have b4 := copyParameterWord_block 4 s4 (by simpa using p4) src4 dst4
  simpa [copyRootState, s1, s2, s3, s4, s5] using
    (((b0.append b1).append b2).append b3).append b4

theorem copyParameter_pc (state : MachineState) (pc : state.pc = 0x1098) :
    (copyRootState state).pc = 0x10c0 := by
  have p1 := copyParameterWord_pc 0 state (by simpa using pc)
  have p2 := copyParameterWord_pc 1 (copyWordState 0 state) (by simpa using p1)
  have p3 := copyParameterWord_pc 2 (copyWordState 1 (copyWordState 0 state))
    (by simpa using p2)
  have p4 := copyParameterWord_pc 3
    (copyWordState 2 (copyWordState 1 (copyWordState 0 state)))
    (by simpa using p3)
  have p5 := copyParameterWord_pc 4
    (copyWordState 3 (copyWordState 2 (copyWordState 1 (copyWordState 0 state))))
    (by simpa using p4)
  simpa [copyRootState] using p5

def setupAndBothState (state : MachineState) : MachineState :=
  copyRootState (parameterPointers (setupAndRootState state))

theorem setupAndBoth_block (state : MachineState) (pc : state.pc = 0x1000) :
    OrdinarySteps SphincsImages.verify state 45 (setupAndBothState state) := by
  let afterRoot := setupAndRootState state
  let afterPointers := parameterPointers afterRoot
  have first := setupAndRoot_block state pc
  have jumpPc := SphincsVerifierCommitment.entry_next_pc state pc
  have headerPc := SphincsVerifierSlots.header_next_pc
    (execInstrBr state (.JAL .x0 16)) jumpPc
  have pointerPc := addressSetup_pc
    (SphincsVerifierSlots.headerState (execInstrBr state (.JAL .x0 16))) headerPc
  have rootPc := copyRoot_pc
    (addressSetupState (SphincsVerifierSlots.headerState (execInstrBr state (.JAL .x0 16))))
    pointerPc
  have pointers := parameterPointers_block afterRoot rootPc
  have secondPc := parameterPointers_pc afterRoot rootPc
  have secondRegs := parameterPointers_regs afterRoot
  have copied := copyParameter_block afterPointers secondPc secondRegs.1 secondRegs.2
  simpa [setupAndBothState, afterRoot, afterPointers] using
    (first.append pointers).append copied

theorem setupAndBoth_pc (state : MachineState) (pc : state.pc = 0x1000) :
    (setupAndBothState state).pc = 0x10c0 := by
  have jumpPc := SphincsVerifierCommitment.entry_next_pc state pc
  have headerPc := SphincsVerifierSlots.header_next_pc
    (execInstrBr state (.JAL .x0 16)) jumpPc
  have pointerPc := addressSetup_pc
    (SphincsVerifierSlots.headerState (execInstrBr state (.JAL .x0 16))) headerPc
  have rootPc := copyRoot_pc
    (addressSetupState (SphincsVerifierSlots.headerState (execInstrBr state (.JAL .x0 16))))
    pointerPc
  have parameterPc := parameterPointers_pc (setupAndRootState state) rootPc
  simpa [setupAndBothState] using
    copyParameter_pc (parameterPointers (setupAndRootState state)) parameterPc

/-- info: 'SigGolfCandidate.SphincsVerifierCopyParameter.setupAndBoth_block' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms setupAndBoth_block

end SigGolfCandidate.SphincsVerifierCopyParameter
