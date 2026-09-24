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

private theorem tag_scratch (state : MachineState) (slot : Fin 4) :
    (SphincsVerifierHeader.tagState state).getMem
      (BitVec.ofNat 64 (0x43000 + 8 * slot.val)) =
      state.getMem (BitVec.ofNat 64 (0x43000 + 8 * slot.val)) := by
  simp only [SphincsVerifierHeader.tagState, execInstrBr,
    MachineState.getMem_setPC]
  rw [SphincsVerifierHeader.tagBeforeStore_pointer]
  rw [setWord32_eq]
  rw [MachineState.getMem_setMem_ne (by fin_cases slot <;> decide)]
  exact SphincsVerifierHeader.tagBeforeStore_memory state _

private theorem position_scratch (state : MachineState) (slot : Fin 4)
    (destination : state.getReg .x7 = 0x40000) :
    (SphincsVerifierHeader.positionState state).getMem
      (BitVec.ofNat 64 (0x43000 + 8 * slot.val)) =
      state.getMem (BitVec.ofNat 64 (0x43000 + 8 * slot.val)) := by
  simp only [SphincsVerifierHeader.positionState, execInstrBr,
    MachineState.getMem_setPC]
  rw [SphincsVerifierHeader.positionBeforeStore_pointer, destination]
  rw [setWord32_eq]
  rw [MachineState.getMem_setMem_ne (by fin_cases slot <;> decide)]
  exact SphincsVerifierHeader.positionBeforeStore_memory state _

private theorem tree_scratch (state : MachineState) (slot : Fin 4)
    (destination : state.getReg .x7 = 0x40000) :
    (SphincsVerifierHeader.treeState state).getMem
      (BitVec.ofNat 64 (0x43000 + 8 * slot.val)) =
      state.getMem (BitVec.ofNat 64 (0x43000 + 8 * slot.val)) := by
  simp only [SphincsVerifierHeader.treeState, execInstrBr,
    MachineState.getMem_setPC]
  rw [SphincsVerifierHeader.treeBeforeStore_pointer, destination]
  rw [MachineState.getMem_setMem_ne (by fin_cases slot <;> decide)]
  exact SphincsVerifierHeader.treeBeforeStore_memory state _

private theorem index_scratch (state : MachineState) (slot : Fin 4)
    (destination : state.getReg .x7 = 0x40000) :
    (SphincsVerifierHeader.indexState state).getMem
      (BitVec.ofNat 64 (0x43000 + 8 * slot.val)) =
      state.getMem (BitVec.ofNat 64 (0x43000 + 8 * slot.val)) := by
  simp only [SphincsVerifierHeader.indexState, execInstrBr,
    MachineState.getMem_setPC]
  rw [SphincsVerifierHeader.indexBeforeStore_pointer, destination]
  rw [setWord32_eq]
  rw [MachineState.getMem_setMem_ne (by fin_cases slot <;> decide)]
  exact SphincsVerifierHeader.indexBeforeStore_memory state _

theorem header_scratch (state : MachineState) (slot : Fin 4) :
    (SphincsVerifierHeader.headerState state).getMem
      (BitVec.ofNat 64 (0x43000 + 8 * slot.val)) =
      state.getMem (BitVec.ofNat 64 (0x43000 + 8 * slot.val)) := by
  let afterTag := SphincsVerifierHeader.tagState state
  let afterPosition := SphincsVerifierHeader.positionState afterTag
  let afterTree := SphincsVerifierHeader.treeState afterPosition
  have tagPointer := SphincsVerifierHeader.tag_hash_pointer state
  have positionPointer : afterPosition.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.position_hash_pointer afterTag).trans tagPointer
  have treePointer : afterTree.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.tree_hash_pointer afterPosition).trans positionPointer
  change (SphincsVerifierHeader.indexState afterTree).getMem _ = state.getMem _
  rw [index_scratch afterTree slot treePointer,
    tree_scratch afterPosition slot positionPointer,
    position_scratch afterTag slot tagPointer,
    tag_scratch state slot]

/-- Header construction changes only its three 64-bit buffer words. -/
theorem header_mem_frame (state : MachineState) (read : Word)
    (first : read ≠ 0x40000) (second : read ≠ 0x40008)
    (third : read ≠ 0x40010) :
    (SphincsVerifierHeader.headerState state).getMem read =
      state.getMem read := by
  let tagged := SphincsVerifierHeader.tagState state
  let positioned := SphincsVerifierHeader.positionState tagged
  let treed := SphincsVerifierHeader.treeState positioned
  have tagPointer := SphincsVerifierHeader.tag_hash_pointer state
  have positionPointer : positioned.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.position_hash_pointer tagged).trans tagPointer
  have treePointer : treed.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.tree_hash_pointer positioned).trans positionPointer
  change (SphincsVerifierHeader.indexState treed).getMem read = state.getMem read
  simp only [SphincsVerifierHeader.indexState, execInstrBr,
    MachineState.getMem_setPC]
  rw [SphincsVerifierHeader.indexBeforeStore_pointer, treePointer,
    setWord32_eq]
  have indexAddress : (0x40000 : Word) + signExtend12 (16 : BitVec 12) =
      0x40010 := by decide
  rw [indexAddress,
    show alignToDword (0x40010 : Word) = 0x40010 by decide,
    MachineState.getMem_setMem_ne third,
    SphincsVerifierHeader.indexBeforeStore_memory]
  change (SphincsVerifierHeader.treeState positioned).getMem read =
    state.getMem read
  simp only [SphincsVerifierHeader.treeState, execInstrBr,
    MachineState.getMem_setPC]
  rw [SphincsVerifierHeader.treeBeforeStore_pointer, positionPointer]
  have treeAddress : (0x40000 : Word) + signExtend12 (8 : BitVec 12) =
      0x40008 := by decide
  rw [treeAddress, MachineState.getMem_setMem_ne second,
    SphincsVerifierHeader.treeBeforeStore_memory]
  change (SphincsVerifierHeader.positionState tagged).getMem read =
    state.getMem read
  simp only [SphincsVerifierHeader.positionState, execInstrBr,
    MachineState.getMem_setPC]
  rw [SphincsVerifierHeader.positionBeforeStore_pointer, tagPointer,
    setWord32_eq]
  have positionAddress : (0x40000 : Word) + signExtend12 (4 : BitVec 12) =
      0x40004 := by decide
  rw [positionAddress]
  have positionDword : alignToDword (0x40004 : Word) = 0x40000 := by decide
  rw [positionDword, MachineState.getMem_setMem_ne first,
    SphincsVerifierHeader.positionBeforeStore_memory]
  change (SphincsVerifierHeader.tagState state).getMem read =
    state.getMem read
  simp only [SphincsVerifierHeader.tagState, execInstrBr,
    MachineState.getMem_setPC]
  rw [SphincsVerifierHeader.tagBeforeStore_pointer, setWord32_eq,
    show (0x40000 : Word) + signExtend12 (0 : BitVec 12) = 0x40000 by decide,
    show alignToDword (0x40000 : Word) = 0x40000 by decide,
    MachineState.getMem_setMem_ne first,
    SphincsVerifierHeader.tagBeforeStore_memory]

theorem firstHash_scratch (state : MachineState) (slot : Fin 4) :
    (firstHashState state).getMem
      (BitVec.ofNat 64 (0x43000 + 8 * slot.val)) = 0 := by
  rw [firstHashState, SphincsVerifierHashSetup.hashSetupState,
    SphincsVerifierHashSetup.hashRegisters_memory,
    header_scratch]
  exact setupAndBoth_scratch state slot

theorem setupAndBoth_publicKey_frame (state : MachineState) (index : Fin 2) :
    (setupAndBothState state).getMem
      (BitVec.ofNat 64 (0x40 + 8 * index.val)) =
      state.getMem (BitVec.ofNat 64 (0x40 + 8 * index.val)) := by
  let read := BitVec.ofNat 64 (0x40 + 8 * index.val)
  let jumped := execInstrBr state (.JAL .x0 16)
  let scratch := SphincsVerifierSlots.headerState jumped
  let firstPointers := addressSetupState scratch
  let firstCopy := copyRootState firstPointers
  let secondPointers := parameterPointers firstCopy
  have firstDestination := (addressSetup_regs scratch).2
  have secondDestination := (parameterPointers_regs firstCopy).2
  have firstOutside : ∀ offset : Fin 5, read ≠ alignToDword
      (firstPointers.getReg .x7 + signExtend12
        (4#12 * BitVec.ofNat 12 offset.val)) := by
    intro offset
    rw [firstDestination]
    fin_cases index <;> fin_cases offset <;> decide
  have secondOutside : ∀ offset : Fin 5, read ≠ alignToDword
      (secondPointers.getReg .x7 + signExtend12
        (4#12 * BitVec.ofNat 12 offset.val)) := by
    intro offset
    rw [secondDestination]
    fin_cases index <;> fin_cases offset <;> decide
  change (copyRootState secondPointers).getMem read = state.getMem read
  rw [copyRoot_mem_frame secondPointers read secondOutside,
    parameterPointers_memory,
    copyRoot_mem_frame firstPointers read firstOutside,
    addressSetup_memory]
  change (SphincsVerifierSlots.headerState jumped).getMem read =
    state.getMem read
  simp only [SphincsVerifierSlots.headerState]
  have slotOutside (slot : Fin 4) :
      read ≠ BitVec.ofNat 64 (0x43000 + 8 * slot.val) := by
    fin_cases index <;> fin_cases slot <;> decide
  rw [SphincsVerifierSlots.slot_memory 3,
    if_neg (slotOutside 3), SphincsVerifierSlots.slot_memory 2,
    if_neg (slotOutside 2), SphincsVerifierSlots.slot_memory 1,
    if_neg (slotOutside 1), SphincsVerifierSlots.slot_memory 0,
    if_neg (slotOutside 0)]
  simp [jumped, execInstrBr]

theorem firstHash_publicKey_frame (state : MachineState) (index : Fin 2) :
    (firstHashState state).getMem
      (BitVec.ofNat 64 (0x40 + 8 * index.val)) =
      state.getMem (BitVec.ofNat 64 (0x40 + 8 * index.val)) := by
  let read := BitVec.ofNat 64 (0x40 + 8 * index.val)
  change (SphincsVerifierHashSetup.hashRegistersState
    (SphincsVerifierHeader.headerState (setupAndBothState state))).getMem
      read = state.getMem read
  rw [SphincsVerifierHashSetup.hashRegisters_memory]
  have outside0 : read ≠ 0x40000 := by fin_cases index <;> decide
  have outside8 : read ≠ 0x40008 := by fin_cases index <;> decide
  have outside16 : read ≠ 0x40010 := by fin_cases index <;> decide
  rw [header_mem_frame _ _ outside0 outside8 outside16,
    setupAndBoth_publicKey_frame]

theorem position_value_after_copies (state : MachineState) :
    (SphincsVerifierHeader.positionState
      (SphincsVerifierHeader.tagState (setupAndBothState state))).getWord32
        0x40004 = 0 := by
  let copied := setupAndBothState state
  have tagPointer := SphincsVerifierHeader.tag_hash_pointer copied
  have positionZero : (SphincsVerifierHeader.tagState copied).getMem
      (0x43010#64) = 0 := by
    have h := (tag_scratch copied 2).trans (setupAndBoth_scratch state 2)
    simpa using h
  exact SphincsVerifierHeader.position_value
    (SphincsVerifierHeader.tagState copied) tagPointer positionZero

theorem tree_value_after_copies (state : MachineState) :
    (SphincsVerifierHeader.treeState
      (SphincsVerifierHeader.positionState
        (SphincsVerifierHeader.tagState (setupAndBothState state)))).getMem
          0x40008 = 0 := by
  let copied := setupAndBothState state
  let tagged := SphincsVerifierHeader.tagState copied
  let positioned := SphincsVerifierHeader.positionState tagged
  have tagPointer := SphincsVerifierHeader.tag_hash_pointer copied
  have positionPointer : positioned.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.position_hash_pointer tagged).trans tagPointer
  have treeZero : positioned.getMem (0x43008#64) = 0 := by
    have h := (position_scratch tagged 1 tagPointer).trans
      ((tag_scratch copied 1).trans (setupAndBoth_scratch state 1))
    simpa using h
  exact SphincsVerifierHeader.tree_value positioned positionPointer treeZero

theorem index_value_after_copies (state : MachineState) :
    (SphincsVerifierHeader.headerState (setupAndBothState state)).getWord32
      0x40010 = 0 := by
  let copied := setupAndBothState state
  let tagged := SphincsVerifierHeader.tagState copied
  let positioned := SphincsVerifierHeader.positionState tagged
  let treed := SphincsVerifierHeader.treeState positioned
  have tagPointer := SphincsVerifierHeader.tag_hash_pointer copied
  have positionPointer : positioned.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.position_hash_pointer tagged).trans tagPointer
  have treePointer : treed.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.tree_hash_pointer positioned).trans positionPointer
  have indexZero : treed.getMem (0x43018#64) = 0 := by
    have h := (tree_scratch positioned 3 positionPointer).trans
      ((position_scratch tagged 3 tagPointer).trans
        ((tag_scratch copied 3).trans (setupAndBoth_scratch state 3)))
    simpa using h
  exact SphincsVerifierHeader.index_value treed treePointer indexZero

private theorem position_preserves_tag (state : MachineState)
    (destination : state.getReg .x7 = 0x40000) :
    (SphincsVerifierHeader.positionState state).getWord32 0x40000 =
      state.getWord32 0x40000 := by
  simp only [SphincsVerifierHeader.positionState, execInstrBr,
    MachineState.getWord32]
  rw [SphincsVerifierHeader.positionBeforeStore_pointer, destination]
  have other : alignToDword (0x40004 : Word) ≠ alignToDword (0x40000 : Word) ∨
      byteOffset (0x40004 : Word) / 4 ≠ byteOffset (0x40000 : Word) / 4 := by
    decide
  have frame := getWord32_setWord32_other
    (SphincsVerifierHeader.positionBeforeStore state) 0x40004 0x40000
    (BitVec.setWidth 32 ((SphincsVerifierHeader.positionBeforeStore state).getReg .x6))
    other
  simpa [MachineState.getWord32, signExtend12,
    SphincsVerifierHeader.positionBeforeStore_memory] using frame

theorem tag_word_frame (state : MachineState) (read : Word)
    (other : alignToDword (0x40000 : Word) ≠ alignToDword read ∨
      byteOffset (0x40000 : Word) / 4 ≠ byteOffset read / 4) :
    (SphincsVerifierHeader.tagState state).getWord32 read =
      state.getWord32 read := by
  simp only [SphincsVerifierHeader.tagState, execInstrBr,
    MachineState.getWord32]
  rw [SphincsVerifierHeader.tagBeforeStore_pointer]
  have frame := getWord32_setWord32_other
    (SphincsVerifierHeader.tagBeforeStore state) 0x40000 read
    (BitVec.setWidth 32 ((SphincsVerifierHeader.tagBeforeStore state).getReg .x6))
    other
  simpa [MachineState.getWord32, signExtend12,
    SphincsVerifierHeader.tagBeforeStore_memory] using frame

theorem position_word_frame (state : MachineState) (read : Word)
    (destination : state.getReg .x7 = 0x40000)
    (other : alignToDword (0x40004 : Word) ≠ alignToDword read ∨
      byteOffset (0x40004 : Word) / 4 ≠ byteOffset read / 4) :
    (SphincsVerifierHeader.positionState state).getWord32 read =
      state.getWord32 read := by
  simp only [SphincsVerifierHeader.positionState, execInstrBr,
    MachineState.getWord32]
  rw [SphincsVerifierHeader.positionBeforeStore_pointer, destination]
  have frame := getWord32_setWord32_other
    (SphincsVerifierHeader.positionBeforeStore state) 0x40004 read
    (BitVec.setWidth 32 ((SphincsVerifierHeader.positionBeforeStore state).getReg .x6))
    other
  simpa [MachineState.getWord32, signExtend12,
    SphincsVerifierHeader.positionBeforeStore_memory] using frame

theorem tree_word_frame (state : MachineState) (read : Word)
    (destination : state.getReg .x7 = 0x40000)
    (other : alignToDword read ≠ (0x40008 : Word)) :
    (SphincsVerifierHeader.treeState state).getWord32 read =
      state.getWord32 read := by
  simp only [SphincsVerifierHeader.treeState, execInstrBr,
    MachineState.getWord32, MachineState.getMem_setPC]
  rw [SphincsVerifierHeader.treeBeforeStore_pointer, destination]
  have address : (0x40000 : Word) + signExtend12 (8 : BitVec 12) = 0x40008 := by
    decide
  rw [address, MachineState.getMem_setMem_ne other,
    SphincsVerifierHeader.treeBeforeStore_memory]

theorem index_word_frame (state : MachineState) (read : Word)
    (destination : state.getReg .x7 = 0x40000)
    (other : alignToDword (0x40010 : Word) ≠ alignToDword read ∨
      byteOffset (0x40010 : Word) / 4 ≠ byteOffset read / 4) :
    (SphincsVerifierHeader.indexState state).getWord32 read =
      state.getWord32 read := by
  simp only [SphincsVerifierHeader.indexState, execInstrBr,
    MachineState.getWord32]
  rw [SphincsVerifierHeader.indexBeforeStore_pointer, destination]
  have frame := getWord32_setWord32_other
    (SphincsVerifierHeader.indexBeforeStore state) 0x40010 read
    (BitVec.setWidth 32 ((SphincsVerifierHeader.indexBeforeStore state).getReg .x6))
    other
  simpa [MachineState.getWord32, signExtend12,
    SphincsVerifierHeader.indexBeforeStore_memory] using frame

private def HeaderUntouched (read : Word) : Prop :=
  (alignToDword (0x40000 : Word) ≠ alignToDword read ∨
    byteOffset (0x40000 : Word) / 4 ≠ byteOffset read / 4) ∧
  (alignToDword (0x40004 : Word) ≠ alignToDword read ∨
    byteOffset (0x40004 : Word) / 4 ≠ byteOffset read / 4) ∧
  alignToDword read ≠ (0x40008 : Word) ∧
  (alignToDword (0x40010 : Word) ≠ alignToDword read ∨
    byteOffset (0x40010 : Word) / 4 ≠ byteOffset read / 4)

theorem header_word_frame (state : MachineState) (read : Word)
    (untouched : HeaderUntouched read) :
    (SphincsVerifierHeader.headerState state).getWord32 read =
      state.getWord32 read := by
  let tagged := SphincsVerifierHeader.tagState state
  let positioned := SphincsVerifierHeader.positionState tagged
  let treed := SphincsVerifierHeader.treeState positioned
  have tagPointer := SphincsVerifierHeader.tag_hash_pointer state
  have positionPointer : positioned.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.position_hash_pointer tagged).trans tagPointer
  have treePointer : treed.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.tree_hash_pointer positioned).trans positionPointer
  change (SphincsVerifierHeader.indexState treed).getWord32 read =
    state.getWord32 read
  rw [index_word_frame treed read treePointer untouched.2.2.2,
    tree_word_frame positioned read positionPointer untouched.2.2.1,
    position_word_frame tagged read tagPointer untouched.2.1,
    tag_word_frame state read untouched.1]

theorem header_root_frame (state : MachineState) (index : Fin 5) :
    (SphincsVerifierHeader.headerState state).getWord32
      (BitVec.ofNat 64 (0x40014 + 4 * index.val)) =
      state.getWord32 (BitVec.ofNat 64 (0x40014 + 4 * index.val)) := by
  apply header_word_frame
  fin_cases index <;> simp [HeaderUntouched, alignToDword, byteOffset]

theorem header_parameter_frame (state : MachineState) (index : Fin 5) :
    (SphincsVerifierHeader.headerState state).getWord32
      (BitVec.ofNat 64 (0x40028 + 4 * index.val)) =
      state.getWord32 (BitVec.ofNat 64 (0x40028 + 4 * index.val)) := by
  apply header_word_frame
  fin_cases index <;> simp [HeaderUntouched, alignToDword, byteOffset]

theorem firstHash_root_frame (state : MachineState) (index : Fin 5) :
    (firstHashState state).getWord32
      (BitVec.ofNat 64 (0x40014 + 4 * index.val)) =
      (setupAndBothState state).getWord32
        (BitVec.ofNat 64 (0x40014 + 4 * index.val)) := by
  change (SphincsVerifierHashSetup.hashRegistersState
    (SphincsVerifierHeader.headerState (setupAndBothState state))).getWord32 _ = _
  simp only [MachineState.getWord32,
    SphincsVerifierHashSetup.hashRegisters_memory]
  exact header_root_frame (setupAndBothState state) index

theorem firstHash_parameter_frame (state : MachineState) (index : Fin 5) :
    (firstHashState state).getWord32
      (BitVec.ofNat 64 (0x40028 + 4 * index.val)) =
      (setupAndBothState state).getWord32
        (BitVec.ofNat 64 (0x40028 + 4 * index.val)) := by
  change (SphincsVerifierHashSetup.hashRegistersState
    (SphincsVerifierHeader.headerState (setupAndBothState state))).getWord32 _ = _
  simp only [MachineState.getWord32,
    SphincsVerifierHashSetup.hashRegisters_memory]
  exact header_parameter_frame (setupAndBothState state) index

theorem firstHash_tag (state : MachineState) :
    (firstHashState state).getWord32 0x40000 = 0xd01 := by
  let copied := setupAndBothState state
  let tagged := SphincsVerifierHeader.tagState copied
  let positioned := SphincsVerifierHeader.positionState tagged
  let treed := SphincsVerifierHeader.treeState positioned
  have tagPointer := SphincsVerifierHeader.tag_hash_pointer copied
  have positionPointer : positioned.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.position_hash_pointer tagged).trans tagPointer
  have treePointer : treed.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.tree_hash_pointer positioned).trans positionPointer
  change (SphincsVerifierHashSetup.hashRegistersState
    (SphincsVerifierHeader.indexState treed)).getWord32 0x40000 = 0xd01
  simp only [MachineState.getWord32,
    SphincsVerifierHashSetup.hashRegisters_memory]
  change (SphincsVerifierHeader.indexState treed).getWord32 0x40000 = 0xd01
  rw [index_word_frame treed 0x40000 treePointer (by decide),
    tree_word_frame positioned 0x40000 positionPointer (by decide),
    position_preserves_tag tagged tagPointer]
  exact tag_value_after_copies state

theorem firstHash_position (state : MachineState) :
    (firstHashState state).getWord32 0x40004 = 0 := by
  let copied := setupAndBothState state
  let tagged := SphincsVerifierHeader.tagState copied
  let positioned := SphincsVerifierHeader.positionState tagged
  let treed := SphincsVerifierHeader.treeState positioned
  have tagPointer := SphincsVerifierHeader.tag_hash_pointer copied
  have positionPointer : positioned.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.position_hash_pointer tagged).trans tagPointer
  have treePointer : treed.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.tree_hash_pointer positioned).trans positionPointer
  change (SphincsVerifierHashSetup.hashRegistersState
    (SphincsVerifierHeader.indexState treed)).getWord32 0x40004 = 0
  simp only [MachineState.getWord32,
    SphincsVerifierHashSetup.hashRegisters_memory]
  change (SphincsVerifierHeader.indexState treed).getWord32 0x40004 = 0
  rw [index_word_frame treed 0x40004 treePointer (by decide),
    tree_word_frame positioned 0x40004 positionPointer (by decide)]
  exact position_value_after_copies state

theorem firstHash_tree (state : MachineState) :
    (firstHashState state).getMem 0x40008 = 0 := by
  let copied := setupAndBothState state
  let tagged := SphincsVerifierHeader.tagState copied
  let positioned := SphincsVerifierHeader.positionState tagged
  let treed := SphincsVerifierHeader.treeState positioned
  have tagPointer := SphincsVerifierHeader.tag_hash_pointer copied
  have positionPointer : positioned.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.position_hash_pointer tagged).trans tagPointer
  have treePointer : treed.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.tree_hash_pointer positioned).trans positionPointer
  change (SphincsVerifierHashSetup.hashRegistersState
    (SphincsVerifierHeader.indexState treed)).getMem 0x40008 = 0
  rw [SphincsVerifierHashSetup.hashRegisters_memory]
  simp only [SphincsVerifierHeader.indexState, execInstrBr,
    MachineState.getMem_setPC]
  rw [SphincsVerifierHeader.indexBeforeStore_pointer, treePointer, setWord32_eq]
  rw [MachineState.getMem_setMem_ne (by decide),
    SphincsVerifierHeader.indexBeforeStore_memory]
  exact tree_value_after_copies state

theorem firstHash_index (state : MachineState) :
    (firstHashState state).getWord32 0x40010 = 0 := by
  change (SphincsVerifierHashSetup.hashRegistersState
    (SphincsVerifierHeader.headerState (setupAndBothState state))).getWord32 0x40010 = 0
  simp only [MachineState.getWord32,
    SphincsVerifierHashSetup.hashRegisters_memory]
  exact index_value_after_copies state

/-- info: 'SigGolfCandidate.SphincsVerifierHashMemory.setupAndBoth_scratch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms setupAndBoth_scratch

/-- info: 'SigGolfCandidate.SphincsVerifierHashMemory.firstHash_tag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms firstHash_tag

/-- info: 'SigGolfCandidate.SphincsVerifierHashMemory.firstHash_position' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms firstHash_position

/-- info: 'SigGolfCandidate.SphincsVerifierHashMemory.firstHash_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms firstHash_tree

/-- info: 'SigGolfCandidate.SphincsVerifierHashMemory.firstHash_index' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms firstHash_index

/-- info: 'SigGolfCandidate.SphincsVerifierHashMemory.firstHash_root_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms firstHash_root_frame

/-- info: 'SigGolfCandidate.SphincsVerifierHashMemory.firstHash_parameter_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms firstHash_parameter_frame

/-- info: 'SigGolfCandidate.SphincsVerifierHashMemory.header_mem_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms header_mem_frame

/-- info: 'SigGolfCandidate.SphincsVerifierHashMemory.setupAndBoth_publicKey_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms setupAndBoth_publicKey_frame

/-- info: 'SigGolfCandidate.SphincsVerifierHashMemory.firstHash_publicKey_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms firstHash_publicKey_frame

end SigGolfCandidate.SphincsVerifierHashMemory
