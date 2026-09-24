import SigGolfCandidate.SphincsVerifierCopyParameterMemory

/-!
# Commitment hash header

The verifier writes its domain tag after the two 20-byte witness fields.
The first ten instructions of this header are certified against the exact
image; the remaining header fields follow in later blocks.
-/

namespace SigGolfCandidate.SphincsVerifierHeader
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierPrefix
open SigGolfCandidate.SphincsVerifierCopyMemory

@[simp] private theorem getWord32_setPC (state : MachineState) (pc address : Word) :
    (state.setPC pc).getWord32 address = state.getWord32 address := rfl

@[simp] private theorem getReg_setWord32 (state : MachineState) (address : Word)
    (value : BitVec 32) (register : Reg) :
    (state.setWord32 address value).getReg register = state.getReg register := rfl

@[simp] private theorem getReg_setMem (state : MachineState) (address value : Word)
    (register : Reg) :
    (state.setMem address value).getReg register = state.getReg register := rfl

def tagBeforeStore (state : MachineState) : MachineState :=
  let state := execInstrBr state (.LUI .x6 0x1)
  let state := execInstrBr state (.ADDI .x6 .x6 (-767))
  let state := execInstrBr state (.LUI .x28 0x43)
  let state := execInstrBr state (.ADDI .x28 .x28 0)
  let state := execInstrBr state (.LD .x7 .x28 0)
  let state := execInstrBr state (.SLLI .x7 .x7 16)
  let state := execInstrBr state (.ADD .x6 .x6 .x7)
  let state := execInstrBr state (.LUI .x7 0x40)
  execInstrBr state (.ADDI .x7 .x7 0)

def tagState (state : MachineState) : MachineState :=
  execInstrBr (tagBeforeStore state) (.SW .x7 .x6 0)

theorem tag_block (state : MachineState) (pc : state.pc = 0x10c0) :
    OrdinarySteps SphincsImages.verify state 10 (tagState state) := by
  let s1 := execInstrBr state (.LUI .x6 0x1)
  let s2 := execInstrBr s1 (.ADDI .x6 .x6 (-767))
  let s3 := execInstrBr s2 (.LUI .x28 0x43)
  let s4 := execInstrBr s3 (.ADDI .x28 .x28 0)
  let s5 := execInstrBr s4 (.LD .x7 .x28 0)
  let s6 := execInstrBr s5 (.SLLI .x7 .x7 16)
  let s7 := execInstrBr s6 (.ADD .x6 .x6 .x7)
  let s8 := execInstrBr s7 (.LUI .x7 0x40)
  let s9 := execInstrBr s8 (.ADDI .x7 .x7 0)
  let s10 := execInstrBr s9 (.SW .x7 .x6 0)
  have p1 : s1.pc = 0x10c4 := by simp [s1, execInstrBr, MachineState.setPC, pc]
  have p2 : s2.pc = 0x10c8 := by simp [s2, execInstrBr, MachineState.setPC, p1]
  have p3 : s3.pc = 0x10cc := by simp [s3, execInstrBr, MachineState.setPC, p2]
  have p4 : s4.pc = 0x10d0 := by simp [s4, execInstrBr, MachineState.setPC, p3]
  have p5 : s5.pc = 0x10d4 := by simp [s5, execInstrBr, MachineState.setPC, p4]
  have p6 : s6.pc = 0x10d8 := by simp [s6, execInstrBr, MachineState.setPC, p5]
  have p7 : s7.pc = 0x10dc := by simp [s7, execInstrBr, MachineState.setPC, p6]
  have p8 : s8.pc = 0x10e0 := by simp [s8, execInstrBr, MachineState.setPC, p7]
  have p9 : s9.pc = 0x10e4 := by simp [s9, execInstrBr, MachineState.setPC, p8]
  apply OrdinarySteps.step state s1 _ (.base (.LUI .x6 0x1)) 9
  · rw [fetch_at state 48 (by decide) (by simpa using pc)]; decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x6 .x6 (-767))) 8
  · rw [fetch_at s1 49 (by decide) (by simpa using p1)]; decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LUI .x28 0x43)) 7
  · rw [fetch_at s2 50 (by decide) (by simpa using p2)]; decide
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x28 .x28 0)) 6
  · rw [fetch_at s3 51 (by decide) (by simpa using p3)]; decide
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.LD .x7 .x28 0)) 5
  · rw [fetch_at s4 52 (by decide) (by simpa using p4)]; decide
  · have pointer : s4.getReg .x28 = 0x43000 := by
      simp [s4, s3, execInstrBr, signExtend12,
        MachineState.getReg_setReg_eq]
    simp [s5, ordinaryStep, memoryArgumentsValid, accessValid,
      rangeValid, signExtend12, pointer, MEMORY_BYTES]
  apply OrdinarySteps.step s5 s6 _ (.base (.SLLI .x7 .x7 16)) 4
  · rw [fetch_at s5 53 (by decide) (by simpa using p5)]; decide
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.ADD .x6 .x6 .x7)) 3
  · rw [fetch_at s6 54 (by decide) (by simpa using p6)]; decide
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.LUI .x7 0x40)) 2
  · rw [fetch_at s7 55 (by decide) (by simpa using p7)]; decide
  · rfl
  apply OrdinarySteps.step s8 s9 _ (.base (.ADDI .x7 .x7 0)) 1
  · rw [fetch_at s8 56 (by decide) (by simpa using p8)]; decide
  · rfl
  apply OrdinarySteps.step s9 s10 _ (.base (.SW .x7 .x6 0)) 0
  · rw [fetch_at s9 57 (by decide) (by simpa using p9)]; decide
  · have pointer : s9.getReg .x7 = 0x40000 := by
      simp [s9, s8, execInstrBr, signExtend12,
        MachineState.getReg_setReg_eq]
    simp [s10, ordinaryStep, memoryArgumentsValid, accessValid,
      rangeValid, signExtend12, pointer, MEMORY_BYTES]
  exact OrdinarySteps.refl _

theorem tag_next_pc (state : MachineState) (pc : state.pc = 0x10c0) :
    (tagState state).pc = 0x10e8 := by
  simp [tagState, tagBeforeStore, execInstrBr, MachineState.setPC, pc]

theorem tag_value (state : MachineState)
    (layerZero : state.getMem 0x43000 = 0) :
    (tagState state).getWord32 0x40000 = 0xd01 := by
  simp [tagState, tagBeforeStore, execInstrBr, signExtend12,
    getWord32_setWord32_same, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne]
  have zero : state.getMem (274432#64) = 0 := by
    have address : (274432#64) = (0x43000 : Word) := by decide
    rw [address]
    exact layerZero
  rw [zero]
  decide

theorem tag_hash_pointer (state : MachineState) :
    (tagState state).getReg .x7 = 0x40000 := by
  simp [tagState, tagBeforeStore, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem tagBeforeStore_memory (state : MachineState) (address : Word) :
    (tagBeforeStore state).getMem address = state.getMem address := by
  simp [tagBeforeStore, execInstrBr]

theorem tagBeforeStore_pointer (state : MachineState) :
    (tagBeforeStore state).getReg .x7 = 0x40000 := by
  simp [tagBeforeStore, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

def positionBeforeStore (state : MachineState) : MachineState :=
  let state := execInstrBr state (.LUI .x28 0x43)
  let state := execInstrBr state (.ADDI .x28 .x28 16)
  execInstrBr state (.LD .x6 .x28 0)

def positionState (state : MachineState) : MachineState :=
  execInstrBr (positionBeforeStore state) (.SW .x7 .x6 4)

theorem position_block (state : MachineState) (pc : state.pc = 0x10e8)
    (destination : state.getReg .x7 = 0x40000) :
    OrdinarySteps SphincsImages.verify state 4 (positionState state) := by
  let s1 := execInstrBr state (.LUI .x28 0x43)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 16)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.SW .x7 .x6 4)
  have p1 : s1.pc = 0x10ec := by simp [s1, execInstrBr, MachineState.setPC, pc]
  have p2 : s2.pc = 0x10f0 := by simp [s2, execInstrBr, MachineState.setPC, p1]
  have p3 : s3.pc = 0x10f4 := by simp [s3, execInstrBr, MachineState.setPC, p2]
  apply OrdinarySteps.step state s1 _ (.base (.LUI .x28 0x43)) 3
  · rw [fetch_at state 58 (by decide) (by simpa using pc)]; decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 16)) 2
  · rw [fetch_at s1 59 (by decide) (by simpa using p1)]; decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 1
  · rw [fetch_at s2 60 (by decide) (by simpa using p2)]; decide
  · have pointer : s2.getReg .x28 = 0x43010 := by
      simp [s2, s1, execInstrBr, signExtend12, MachineState.getReg_setReg_eq]
    simp [s3, ordinaryStep, memoryArgumentsValid, accessValid,
      rangeValid, signExtend12, pointer, MEMORY_BYTES]
  apply OrdinarySteps.step s3 s4 _ (.base (.SW .x7 .x6 4)) 0
  · rw [fetch_at s3 61 (by decide) (by simpa using p3)]; decide
  · have pointer : s3.getReg .x7 = 0x40000 := by
      simp [s3, s2, s1, execInstrBr, MachineState.getReg_setReg_ne, destination]
    simp [s4, ordinaryStep, memoryArgumentsValid, accessValid,
      rangeValid, signExtend12, pointer, MEMORY_BYTES]
  exact OrdinarySteps.refl _

theorem position_next_pc (state : MachineState) (pc : state.pc = 0x10e8) :
    (positionState state).pc = 0x10f8 := by
  simp [positionState, positionBeforeStore, execInstrBr, MachineState.setPC, pc]

theorem position_hash_pointer (state : MachineState) :
    (positionState state).getReg .x7 = state.getReg .x7 := by
  simp [positionState, positionBeforeStore, execInstrBr, signExtend12,
    MachineState.getReg_setReg_ne]

theorem positionBeforeStore_memory (state : MachineState) (address : Word) :
    (positionBeforeStore state).getMem address = state.getMem address := by
  simp [positionBeforeStore, execInstrBr]

theorem positionBeforeStore_pointer (state : MachineState) :
    (positionBeforeStore state).getReg .x7 = state.getReg .x7 := by
  simp [positionBeforeStore, execInstrBr, MachineState.getReg_setReg_ne]

theorem positionBeforeStore_value (state : MachineState)
    (zero : state.getMem (0x43010#64) = 0) :
    (positionBeforeStore state).getReg .x6 = 0 := by
  simp [positionBeforeStore, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq]
  exact zero

theorem position_value (state : MachineState)
    (destination : state.getReg .x7 = 0x40000)
    (zero : state.getMem (0x43010#64) = 0) :
    (positionState state).getWord32 0x40004 = 0 := by
  simp only [positionState, execInstrBr, getWord32_setPC]
  rw [positionBeforeStore_pointer, destination]
  simp only [signExtend12]
  convert getWord32_setWord32_same (positionBeforeStore state) 0x40004
    (BitVec.setWidth 32 ((positionBeforeStore state).getReg .x6)) using 1 <;>
    simp [positionBeforeStore_value state zero]

def treeBeforeStore (state : MachineState) : MachineState :=
  let state := execInstrBr state (.LUI .x28 0x43)
  let state := execInstrBr state (.ADDI .x28 .x28 8)
  execInstrBr state (.LD .x6 .x28 0)

def treeState (state : MachineState) : MachineState :=
  execInstrBr (treeBeforeStore state) (.SD .x7 .x6 8)

theorem tree_block (state : MachineState) (pc : state.pc = 0x10f8)
    (destination : state.getReg .x7 = 0x40000) :
    OrdinarySteps SphincsImages.verify state 4 (treeState state) := by
  let s1 := execInstrBr state (.LUI .x28 0x43)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 8)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.SD .x7 .x6 8)
  have p1 : s1.pc = 0x10fc := by simp [s1, execInstrBr, MachineState.setPC, pc]
  have p2 : s2.pc = 0x1100 := by simp [s2, execInstrBr, MachineState.setPC, p1]
  have p3 : s3.pc = 0x1104 := by simp [s3, execInstrBr, MachineState.setPC, p2]
  apply OrdinarySteps.step state s1 _ (.base (.LUI .x28 0x43)) 3
  · rw [fetch_at state 62 (by decide) (by simpa using pc)]; decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 8)) 2
  · rw [fetch_at s1 63 (by decide) (by simpa using p1)]; decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 1
  · rw [fetch_at s2 64 (by decide) (by simpa using p2)]; decide
  · have pointer : s2.getReg .x28 = 0x43008 := by
      simp [s2, s1, execInstrBr, signExtend12, MachineState.getReg_setReg_eq]
    simp [s3, ordinaryStep, memoryArgumentsValid, accessValid,
      rangeValid, signExtend12, pointer, MEMORY_BYTES]
  apply OrdinarySteps.step s3 s4 _ (.base (.SD .x7 .x6 8)) 0
  · rw [fetch_at s3 65 (by decide) (by simpa using p3)]; decide
  · have pointer : s3.getReg .x7 = 0x40000 := by
      simp [s3, s2, s1, execInstrBr, MachineState.getReg_setReg_ne, destination]
    simp [s4, ordinaryStep, memoryArgumentsValid, accessValid,
      rangeValid, signExtend12, pointer, MEMORY_BYTES]
  exact OrdinarySteps.refl _

theorem tree_next_pc (state : MachineState) (pc : state.pc = 0x10f8) :
    (treeState state).pc = 0x1108 := by
  simp [treeState, treeBeforeStore, execInstrBr, MachineState.setPC, pc]

theorem tree_hash_pointer (state : MachineState) :
    (treeState state).getReg .x7 = state.getReg .x7 := by
  simp [treeState, treeBeforeStore, execInstrBr, signExtend12,
    MachineState.getReg_setReg_ne]

theorem treeBeforeStore_memory (state : MachineState) (address : Word) :
    (treeBeforeStore state).getMem address = state.getMem address := by
  simp [treeBeforeStore, execInstrBr]

theorem treeBeforeStore_pointer (state : MachineState) :
    (treeBeforeStore state).getReg .x7 = state.getReg .x7 := by
  simp [treeBeforeStore, execInstrBr, MachineState.getReg_setReg_ne]

theorem treeBeforeStore_value (state : MachineState)
    (zero : state.getMem (0x43008#64) = 0) :
    (treeBeforeStore state).getReg .x6 = 0 := by
  simp [treeBeforeStore, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq]
  exact zero

theorem tree_value (state : MachineState)
    (destination : state.getReg .x7 = 0x40000)
    (zero : state.getMem (0x43008#64) = 0) :
    (treeState state).getMem 0x40008 = 0 := by
  simp only [treeState, execInstrBr, MachineState.getMem_setPC]
  rw [treeBeforeStore_pointer, destination]
  simp [signExtend12]
  exact treeBeforeStore_value state zero

def indexBeforeStore (state : MachineState) : MachineState :=
  let state := execInstrBr state (.LUI .x28 0x43)
  let state := execInstrBr state (.ADDI .x28 .x28 24)
  execInstrBr state (.LD .x6 .x28 0)

def indexState (state : MachineState) : MachineState :=
  execInstrBr (indexBeforeStore state) (.SW .x7 .x6 16)

theorem index_block (state : MachineState) (pc : state.pc = 0x1108)
    (destination : state.getReg .x7 = 0x40000) :
    OrdinarySteps SphincsImages.verify state 4 (indexState state) := by
  let s1 := execInstrBr state (.LUI .x28 0x43)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 24)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.SW .x7 .x6 16)
  have p1 : s1.pc = 0x110c := by simp [s1, execInstrBr, MachineState.setPC, pc]
  have p2 : s2.pc = 0x1110 := by simp [s2, execInstrBr, MachineState.setPC, p1]
  have p3 : s3.pc = 0x1114 := by simp [s3, execInstrBr, MachineState.setPC, p2]
  apply OrdinarySteps.step state s1 _ (.base (.LUI .x28 0x43)) 3
  · rw [fetch_at state 66 (by decide) (by simpa using pc)]; decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 24)) 2
  · rw [fetch_at s1 67 (by decide) (by simpa using p1)]; decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 1
  · rw [fetch_at s2 68 (by decide) (by simpa using p2)]; decide
  · have pointer : s2.getReg .x28 = 0x43018 := by
      simp [s2, s1, execInstrBr, signExtend12, MachineState.getReg_setReg_eq]
    simp [s3, ordinaryStep, memoryArgumentsValid, accessValid,
      rangeValid, signExtend12, pointer, MEMORY_BYTES]
  apply OrdinarySteps.step s3 s4 _ (.base (.SW .x7 .x6 16)) 0
  · rw [fetch_at s3 69 (by decide) (by simpa using p3)]; decide
  · have pointer : s3.getReg .x7 = 0x40000 := by
      simp [s3, s2, s1, execInstrBr, MachineState.getReg_setReg_ne, destination]
    simp [s4, ordinaryStep, memoryArgumentsValid, accessValid,
      rangeValid, signExtend12, pointer, MEMORY_BYTES]
  exact OrdinarySteps.refl _

theorem index_next_pc (state : MachineState) (pc : state.pc = 0x1108) :
    (indexState state).pc = 0x1118 := by
  simp [indexState, indexBeforeStore, execInstrBr, MachineState.setPC, pc]

theorem index_hash_pointer (state : MachineState) :
    (indexState state).getReg .x7 = state.getReg .x7 := by
  simp [indexState, indexBeforeStore, execInstrBr, signExtend12,
    MachineState.getReg_setReg_ne]

theorem indexBeforeStore_memory (state : MachineState) (address : Word) :
    (indexBeforeStore state).getMem address = state.getMem address := by
  simp [indexBeforeStore, execInstrBr]

theorem indexBeforeStore_pointer (state : MachineState) :
    (indexBeforeStore state).getReg .x7 = state.getReg .x7 := by
  simp [indexBeforeStore, execInstrBr, MachineState.getReg_setReg_ne]

theorem indexBeforeStore_value (state : MachineState)
    (zero : state.getMem (0x43018#64) = 0) :
    (indexBeforeStore state).getReg .x6 = 0 := by
  simp [indexBeforeStore, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq]
  exact zero

theorem index_value (state : MachineState)
    (destination : state.getReg .x7 = 0x40000)
    (zero : state.getMem (0x43018#64) = 0) :
    (indexState state).getWord32 0x40010 = 0 := by
  simp only [indexState, execInstrBr, getWord32_setPC]
  rw [indexBeforeStore_pointer, destination]
  simp only [signExtend12]
  convert getWord32_setWord32_same (indexBeforeStore state) 0x40010
    (BitVec.setWidth 32 ((indexBeforeStore state).getReg .x6)) using 1 <;>
    simp [indexBeforeStore_value state zero]

def headerState (state : MachineState) : MachineState :=
  indexState (treeState (positionState (tagState state)))

theorem header_block (state : MachineState) (pc : state.pc = 0x10c0) :
    OrdinarySteps SphincsImages.verify state 22 (headerState state) := by
  let afterTag := tagState state
  let afterPosition := positionState afterTag
  let afterTree := treeState afterPosition
  have tag := tag_block state pc
  have tagPc := tag_next_pc state pc
  have tagPointer := tag_hash_pointer state
  have position := position_block afterTag tagPc tagPointer
  have positionPc := position_next_pc afterTag tagPc
  have positionPointer : afterPosition.getReg .x7 = 0x40000 :=
    (position_hash_pointer afterTag).trans tagPointer
  have tree := tree_block afterPosition positionPc positionPointer
  have treePc := tree_next_pc afterPosition positionPc
  have treePointer : afterTree.getReg .x7 = 0x40000 :=
    (tree_hash_pointer afterPosition).trans positionPointer
  have index := index_block afterTree treePc treePointer
  simpa [headerState, afterTag, afterPosition, afterTree] using
    ((tag.append position).append tree).append index

theorem header_next_pc (state : MachineState) (pc : state.pc = 0x10c0) :
    (headerState state).pc = 0x1118 := by
  have tagPc := tag_next_pc state pc
  have positionPc := position_next_pc (tagState state) tagPc
  have treePc := tree_next_pc (positionState (tagState state)) positionPc
  have indexPc := index_next_pc (treeState (positionState (tagState state))) treePc
  simpa [headerState] using indexPc

/-- info: 'SigGolfCandidate.SphincsVerifierHeader.tag_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tag_block

/-- info: 'SigGolfCandidate.SphincsVerifierHeader.tag_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tag_value

end SigGolfCandidate.SphincsVerifierHeader
