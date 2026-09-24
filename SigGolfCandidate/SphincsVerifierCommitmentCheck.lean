import SigGolfCandidate.SphincsVerifierLoader

/-!
# Public-key commitment check

The verifier compares the first two 64-bit words of its commitment HASH
answer with the 16-byte public key supplied by the organizer.
-/

namespace SigGolfCandidate.SphincsVerifierCommitmentCheck
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64

/-- Exact image words for the two commitment/public-key comparisons. -/
def comparePrefix : List (BitVec 32) := [
  0x00042337, 0x00030313, 0x04000393, 0x00033503,
  0x0003b583, 0x00b50463, 0xeb9ff06f, 0x00833503,
  0x0083b583, 0x00b50463, 0xea9ff06f]

theorem comparePrefix_eq :
    (SphincsImages.verify.code.drop 77).take 11 = comparePrefix := by
  decide

theorem fetch_compare (state : MachineState) (offset : Fin 11)
    (pc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * (77 + offset.val))) :
    fetch SphincsImages.verify state =
      (comparePrefix[offset.val]?).bind decodeInstruction := by
  have small : 0x1000 + 4 * (77 + offset.val) < 2 ^ 64 := by omega
  simp only [fetch, pc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
  have start : ¬ (0x1000 + 4 * (77 + offset.val) < 0x1000) := by omega
  have aligned : (0x1000 + 4 * (77 + offset.val)) % 4 = 0 := by omega
  simp only [start, decide_false, aligned, Bool.false_or]
  have index : (0x1000 + 4 * (77 + offset.val) - 0x1000) / 4 =
      77 + offset.val := by omega
  rw [index]
  rw [← List.getElem?_drop]
  rw [← List.getElem?_take_of_lt offset.isLt, comparePrefix_eq]
  simp

theorem writeHash_low (state : MachineState) (answer : BitVec 256)
    (destination : state.getReg .x12 = 0x42000) :
    (writeHash state answer).getMem 0x42000 =
      answer.extractLsb' 0 64 := by
  simp [writeHash, MachineState.writeWords_cons, destination]

theorem writeHash_high (state : MachineState) (answer : BitVec 256)
    (destination : state.getReg .x12 = 0x42000) :
    (writeHash state answer).getMem 0x42008 =
      answer.extractLsb' 64 64 := by
  simp [writeHash, MachineState.writeWords_cons, destination]

/-- The success path checks both 64-bit words and skips both rejection jumps. -/
def compareSuccessState (state : MachineState) : MachineState :=
  let state := execInstrBr state (.LUI .x6 0x42)
  let state := execInstrBr state (.ADDI .x6 .x6 0)
  let state := execInstrBr state (.ADDI .x7 .x0 64)
  let state := execInstrBr state (.LD .x10 .x6 0)
  let state := execInstrBr state (.LD .x11 .x7 0)
  let state := execInstrBr state (.BEQ .x10 .x11 8)
  let state := execInstrBr state (.LD .x10 .x6 8)
  let state := execInstrBr state (.LD .x11 .x7 8)
  execInstrBr state (.BEQ .x10 .x11 8)

theorem compareSuccess_block (state : MachineState)
    (pc : state.pc = 0x1134)
    (low : state.getMem 0x42000 = state.getMem 0x40)
    (high : state.getMem 0x42008 = state.getMem 0x48) :
    OrdinarySteps SphincsImages.verify state 9 (compareSuccessState state) := by
  let s1 := execInstrBr state (.LUI .x6 0x42)
  let s2 := execInstrBr s1 (.ADDI .x6 .x6 0)
  let s3 := execInstrBr s2 (.ADDI .x7 .x0 64)
  let s4 := execInstrBr s3 (.LD .x10 .x6 0)
  let s5 := execInstrBr s4 (.LD .x11 .x7 0)
  let s6 := execInstrBr s5 (.BEQ .x10 .x11 8)
  let s7 := execInstrBr s6 (.LD .x10 .x6 8)
  let s8 := execInstrBr s7 (.LD .x11 .x7 8)
  let s9 := execInstrBr s8 (.BEQ .x10 .x11 8)
  have pointer : s3.getReg .x6 = 0x42000 := by
    simp [s3, s2, s1, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  have keyPointer : s3.getReg .x7 = 0x40 := by
    simp [s3, execInstrBr, signExtend12, MachineState.getReg_setReg_eq]
  have memory3 (address : Word) : s3.getMem address = state.getMem address := by
    simp [s3, s2, s1, execInstrBr]
  have firstEqual : s5.getReg .x10 = s5.getReg .x11 := by
    simp [s5, s4, execInstrBr, pointer, keyPointer, signExtend12,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      memory3]
    exact low
  have branch6 : s6 = s5.setPC (s5.pc + 8) := by
    simp [s6, execInstrBr, firstEqual, signExtend13]
  have pointer6 : s6.getReg .x6 = 0x42000 := by
    rw [branch6]
    simpa [s5, s4, execInstrBr, MachineState.getReg_setReg_ne]
      using pointer
  have keyPointer6 : s6.getReg .x7 = 0x40 := by
    rw [branch6]
    simpa [s5, s4, execInstrBr, MachineState.getReg_setReg_ne]
      using keyPointer
  have memory6 (address : Word) : s6.getMem address = state.getMem address := by
    rw [branch6]
    simp [s5, s4, execInstrBr, memory3]
  have secondEqual : s8.getReg .x10 = s8.getReg .x11 := by
    simp [s8, s7, execInstrBr, pointer6, keyPointer6, memory6,
      signExtend12, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne]
    exact high
  have p1 : s1.pc = 0x1138 := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x113c := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x1140 := by simp [s3, execInstrBr, p2]
  have p4 : s4.pc = 0x1144 := by simp [s4, execInstrBr, p3]
  have p5 : s5.pc = 0x1148 := by simp [s5, execInstrBr, p4]
  have p6 : s6.pc = 0x1150 := by
    simp [s6, execInstrBr, firstEqual, p5, signExtend13]
  have p7 : s7.pc = 0x1154 := by simp [s7, execInstrBr, p6]
  have p8 : s8.pc = 0x1158 := by simp [s8, execInstrBr, p7]
  apply OrdinarySteps.step state s1 _ (.base (.LUI .x6 0x42)) 8
  · rw [fetch_compare state ⟨0, by decide⟩ (by simpa using pc)]; decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x6 .x6 0)) 7
  · rw [fetch_compare s1 ⟨1, by decide⟩ (by simpa using p1)]; decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x7 .x0 64)) 6
  · rw [fetch_compare s2 ⟨2, by decide⟩ (by simpa using p2)]; decide
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.LD .x10 .x6 0)) 5
  · rw [fetch_compare s3 ⟨3, by decide⟩ (by simpa using p3)]; decide
  · simp [s4, ordinaryStep, memoryArgumentsValid, accessValid,
      rangeValid, signExtend12, pointer, MEMORY_BYTES]
  apply OrdinarySteps.step s4 s5 _ (.base (.LD .x11 .x7 0)) 4
  · rw [fetch_compare s4 ⟨4, by decide⟩ (by simpa using p4)]; decide
  · have pointer4 : s4.getReg .x7 = 0x40 := by
      simpa [s4, execInstrBr, MachineState.getReg_setReg_ne] using keyPointer
    simp [s5, ordinaryStep, memoryArgumentsValid, accessValid,
      rangeValid, signExtend12, pointer4, MEMORY_BYTES]
  apply OrdinarySteps.step s5 s6 _ (.base (.BEQ .x10 .x11 8)) 3
  · rw [fetch_compare s5 ⟨5, by decide⟩ (by simpa using p5)]; decide
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.LD .x10 .x6 8)) 2
  · rw [fetch_compare s6 ⟨7, by decide⟩ (by simpa using p6)]; decide
  · simp [s7, ordinaryStep, memoryArgumentsValid, accessValid,
      rangeValid, signExtend12, pointer6, MEMORY_BYTES]
  apply OrdinarySteps.step s7 s8 _ (.base (.LD .x11 .x7 8)) 1
  · rw [fetch_compare s7 ⟨8, by decide⟩ (by simpa using p7)]; decide
  · have pointer7 : s7.getReg .x7 = 0x40 := by
      simpa [s7, execInstrBr, MachineState.getReg_setReg_ne]
        using keyPointer6
    simp [s8, ordinaryStep, memoryArgumentsValid, accessValid,
      rangeValid, signExtend12, pointer7, MEMORY_BYTES]
  apply OrdinarySteps.step s8 s9 _ (.base (.BEQ .x10 .x11 8)) 0
  · rw [fetch_compare s8 ⟨9, by decide⟩ (by simpa using p8)]; decide
  · rfl
  exact OrdinarySteps.refl _

/-- info: 'SigGolfCandidate.SphincsVerifierCommitmentCheck.compareSuccess_block' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms compareSuccess_block

/-- info: 'SigGolfCandidate.SphincsVerifierCommitmentCheck.fetch_compare' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms fetch_compare

/-- info: 'SigGolfCandidate.SphincsVerifierCommitmentCheck.writeHash_low' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms writeHash_low

/-- info: 'SigGolfCandidate.SphincsVerifierCommitmentCheck.writeHash_high' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms writeHash_high

end SigGolfCandidate.SphincsVerifierCommitmentCheck
