import SigGolfCandidate.SphincsVerifierCommitment

/-!
# Verifier setup prefix

The generator exposes the first 77 exact instruction words as a short prefix.
This lets symbolic execution cite one checked bytecode equality instead of
re-evaluating the entire 6,954-word verifier image at each program counter.
-/

namespace SigGolfCandidate.SphincsVerifierPrefix
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64

@[simp] private theorem pc_setPC (state : MachineState) (pc : Word) :
    (state.setPC pc).pc = pc := rfl

@[simp] private theorem reg_zero (state : MachineState) : state.getReg .x0 = 0 := rfl

theorem code_at (index : Nat) (bound : index < 77) :
    SphincsImages.verify.code[index]? = SphincsImages.verifyPrefix[index]? := by
  calc
    SphincsImages.verify.code[index]? =
        (SphincsImages.verify.code.take 77)[index]? :=
      (List.getElem?_take_of_lt bound).symm
    _ = SphincsImages.verifyPrefix[index]? := by rw [SphincsImages.verifyPrefix_eq]

theorem fetch_at (state : MachineState) (index : Nat) (bound : index < 77)
    (pc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * index)) :
    fetch SphincsImages.verify state =
      (SphincsImages.verifyPrefix[index]?).bind decodeInstruction := by
  have hpc : 0x1000 + 4 * index < 2 ^ 64 := by omega
  simp only [fetch, pc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpc]
  simp [code_at index bound]

/-- The first setup writes a zero word to the `LAYER` scratch location. -/
def zeroLayerBeforeStore (state : MachineState) : MachineState :=
  let state := execInstrBr state (.ADDI .x6 .x0 0)
  let state := execInstrBr state (.LUI .x28 0x43)
  execInstrBr state (.ADDI .x28 .x28 0)

def zeroLayerState (state : MachineState) : MachineState :=
  execInstrBr (zeroLayerBeforeStore state) (.SD .x28 .x6 0)

theorem zeroLayerBeforeStore_regs (state : MachineState) :
    (zeroLayerBeforeStore state).getReg .x28 = 0x43000 ∧
      (zeroLayerBeforeStore state).getReg .x6 = 0 := by
  simp [zeroLayerBeforeStore, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.getReg_setPC]

theorem zeroLayer_block (state : MachineState) (pc : state.pc = 0x1010) :
    OrdinarySteps SphincsImages.verify state 4 (zeroLayerState state) := by
  let s1 := execInstrBr state (.ADDI .x6 .x0 0)
  let s2 := execInstrBr s1 (.LUI .x28 0x43)
  let s3 := execInstrBr s2 (.ADDI .x28 .x28 0)
  let s4 := execInstrBr s3 (.SD .x28 .x6 0)
  apply OrdinarySteps.step state s1 _ (.base (.ADDI .x6 .x0 0)) 3
  · rw [fetch_at state 4 (by decide) (by simpa using pc)]
    decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x28 0x43)) 2
  · have hp : s1.pc = 0x1014 := by simp [s1, execInstrBr, MachineState.setPC, pc]
    rw [fetch_at s1 5 (by decide) (by simpa using hp)]
    decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x28 .x28 0)) 1
  · have hp : s2.pc = 0x1018 := by simp [s1, s2, execInstrBr, MachineState.setPC, pc]
    rw [fetch_at s2 6 (by decide) (by simpa using hp)]
    decide
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.SD .x28 .x6 0)) 0
  · have hp : s3.pc = 0x101c := by
      simp [s1, s2, s3, execInstrBr, MachineState.setPC, pc]
    rw [fetch_at s3 7 (by decide) (by simpa using hp)]
    decide
  · have haddr : s3.getReg .x28 = 0x43000 := by
      simpa only [s3, s2, s1, zeroLayerBeforeStore] using
        (zeroLayerBeforeStore_regs state).1
    have hvalid : memoryArgumentsValid s3 (.SD .x28 .x6 0) = true := by
      simp [memoryArgumentsValid, accessValid, rangeValid,
        signExtend12, haddr, MEMORY_BYTES]
    simp only [ordinaryStep, hvalid, ite_true, s4]
  exact OrdinarySteps.refl _

theorem zeroLayerBeforeStore_next_pc (state : MachineState) (pc : state.pc = 0x1010) :
    (zeroLayerBeforeStore state).pc = 0x101c := by
  simp [zeroLayerBeforeStore, execInstrBr, pc]

theorem zeroLayer_next_pc (state : MachineState) (pc : state.pc = 0x1010) :
    (zeroLayerState state).pc = 0x1020 := by
  simp [zeroLayerState, execInstrBr, zeroLayerBeforeStore_next_pc state pc]

theorem zeroLayer_value (state : MachineState) :
    (zeroLayerState state).getMem 0x43000 = 0 := by
  obtain ⟨haddr, hvalue⟩ := zeroLayerBeforeStore_regs state
  simp [zeroLayerState, execInstrBr, signExtend12, haddr, hvalue,
    MachineState.getMem_setPC]

/-- info: 'SigGolfCandidate.SphincsVerifierPrefix.zeroLayer_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms zeroLayer_block

end SigGolfCandidate.SphincsVerifierPrefix
