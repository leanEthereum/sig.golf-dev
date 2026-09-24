import SigGolfCandidate.SphincsVerifierHashMemory

/-!
# Commitment HASH bytes

Word-level facts about the verifier's first HASH buffer are converted to the
byte-level invariant required by the organizer's HASH interface.
-/

namespace SigGolfCandidate.SphincsVerifierHashBytes
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierHashMemory
open SigGolfCandidate.SphincsVerifierHashSetup
open SigGolfCandidate.SphincsVerifierCopyParameter
open SigGolfCandidate.SphincsVerifierCopy
open SigGolfCandidate.SphincsVerifierCopyMemory
open SigGolfCandidate.SphincsVerifierCopyParameterMemory

private theorem extractByte_of_extractWord32 (word : Word) (lane : Fin 2)
    (byte : Fin 4) :
    extractByte word (4 * lane.val + byte.val) =
      (extractWord32 word lane.val).extractLsb' (8 * byte.val) 8 := by
  ext i (hi : i < 8)
  simp [extractByte, extractWord32, BitVec.truncate_eq_setWidth]
  have within : 8 * byte.val + i < 32 := by
    have := byte.isLt
    omega
  simp only [within]
  simp only [decide_true, Bool.true_and]
  congr 1
  omega

private theorem extractByte_from_word32 (word : Word) (position : Fin 8) :
    extractByte word position.val =
      (extractWord32 word (position.val / 4)).extractLsb'
        (8 * (position.val % 4)) 8 := by
  fin_cases position <;>
    first
    | exact extractByte_of_extractWord32 word 0 0
    | exact extractByte_of_extractWord32 word 0 1
    | exact extractByte_of_extractWord32 word 0 2
    | exact extractByte_of_extractWord32 word 0 3
    | exact extractByte_of_extractWord32 word 1 0
    | exact extractByte_of_extractWord32 word 1 1
    | exact extractByte_of_extractWord32 word 1 2
    | exact extractByte_of_extractWord32 word 1 3

private theorem rootDestinationByte (state : MachineState) (index : Fin 5)
    (byte : Fin 4) :
    state.getByte (BitVec.ofNat 64 (0x40014 + 4 * index.val + byte.val)) =
      (state.getWord32 (BitVec.ofNat 64 (0x40014 + 4 * index.val))).extractLsb'
        (8 * byte.val) 8 := by
  have split := extractByte_from_word32
    (state.getMem (alignToDword
      (BitVec.ofNat 64 (0x40014 + 4 * index.val + byte.val))))
    ⟨(0x40014 + 4 * index.val + byte.val) % 8,
      Nat.mod_lt _ (by decide)⟩
  fin_cases index <;> fin_cases byte <;>
    simpa [MachineState.getByte, MachineState.getWord32,
      alignToDword, byteOffset] using split

private theorem rootSourceByte (state : MachineState) (index : Fin 5)
    (byte : Fin 4) :
    state.getByte (BitVec.ofNat 64 (0x22ca0 + 4 * index.val + byte.val)) =
      (state.getWord32 (BitVec.ofNat 64 (0x22ca0 + 4 * index.val))).extractLsb'
        (8 * byte.val) 8 := by
  have split := extractByte_from_word32
    (state.getMem (alignToDword
      (BitVec.ofNat 64 (0x22ca0 + 4 * index.val + byte.val))))
    ⟨(0x22ca0 + 4 * index.val + byte.val) % 8,
      Nat.mod_lt _ (by decide)⟩
  fin_cases index <;> fin_cases byte <;>
    simpa [MachineState.getByte, MachineState.getWord32,
      alignToDword, byteOffset] using split

private theorem parameterDestinationByte (state : MachineState) (index : Fin 5)
    (byte : Fin 4) :
    state.getByte (BitVec.ofNat 64 (0x40028 + 4 * index.val + byte.val)) =
      (state.getWord32 (BitVec.ofNat 64 (0x40028 + 4 * index.val))).extractLsb'
        (8 * byte.val) 8 := by
  have split := extractByte_from_word32
    (state.getMem (alignToDword
      (BitVec.ofNat 64 (0x40028 + 4 * index.val + byte.val))))
    ⟨(0x40028 + 4 * index.val + byte.val) % 8,
      Nat.mod_lt _ (by decide)⟩
  fin_cases index <;> fin_cases byte <;>
    simpa [MachineState.getByte, MachineState.getWord32,
      alignToDword, byteOffset] using split

private theorem parameterSourceByte (state : MachineState) (index : Fin 5)
    (byte : Fin 4) :
    state.getByte (BitVec.ofNat 64 (0x22cb4 + 4 * index.val + byte.val)) =
      (state.getWord32 (BitVec.ofNat 64 (0x22cb4 + 4 * index.val))).extractLsb'
        (8 * byte.val) 8 := by
  have split := extractByte_from_word32
    (state.getMem (alignToDword
      (BitVec.ofNat 64 (0x22cb4 + 4 * index.val + byte.val))))
    ⟨(0x22cb4 + 4 * index.val + byte.val) % 8,
      Nat.mod_lt _ (by decide)⟩
  fin_cases index <;> fin_cases byte <;>
    simpa [MachineState.getByte, MachineState.getWord32,
      alignToDword, byteOffset] using split

theorem firstHash_root_byte_frame (state : MachineState) (index : Fin 5)
    (byte : Fin 4) :
    (firstHashState state).getByte
      (BitVec.ofNat 64 (0x40014 + 4 * index.val + byte.val)) =
      (setupAndBothState state).getByte
        (BitVec.ofNat 64 (0x40014 + 4 * index.val + byte.val)) := by
  rw [rootDestinationByte, rootDestinationByte,
    firstHash_root_frame]

theorem firstHash_parameter_byte_frame (state : MachineState) (index : Fin 5)
    (byte : Fin 4) :
    (firstHashState state).getByte
      (BitVec.ofNat 64 (0x40028 + 4 * index.val + byte.val)) =
      (setupAndBothState state).getByte
        (BitVec.ofNat 64 (0x40028 + 4 * index.val + byte.val)) := by
  rw [parameterDestinationByte, parameterDestinationByte,
    firstHash_parameter_frame]

theorem setupAndBoth_root_word (state : MachineState) (index : Fin 5) :
    (setupAndBothState state).getWord32
      (BitVec.ofNat 64 (0x40014 + 4 * index.val)) =
      (addressSetupState
        (SphincsVerifierSlots.headerState (execInstrBr state (.JAL .x0 16)))).getWord32
        (BitVec.ofNat 64 (0x22ca0 + 4 * index.val)) := by
  let pre := addressSetupState
    (SphincsVerifierSlots.headerState (execInstrBr state (.JAL .x0 16)))
  let copied := copyRootState pre
  let pointers := parameterPointers copied
  have rootDst := (addressSetup_regs
    (SphincsVerifierSlots.headerState (execInstrBr state (.JAL .x0 16)))).2
  have rootSrc := (addressSetup_regs
    (SphincsVerifierSlots.headerState (execInstrBr state (.JAL .x0 16)))).1
  have parameterDst := (parameterPointers_regs copied).2
  change (copyRootState pointers).getWord32 _ = pre.getWord32 _
  rw [copyParameter_preserves_root pointers parameterDst index]
  change (parameterPointers copied).getWord32 _ = pre.getWord32 _
  simp only [MachineState.getWord32, parameterPointers_memory]
  change copied.getWord32 _ = pre.getWord32 _
  exact copyRoot_data pre rootSrc rootDst index

theorem setupAndBoth_parameter_word (state : MachineState) (index : Fin 5) :
    (setupAndBothState state).getWord32
      (BitVec.ofNat 64 (0x40028 + 4 * index.val)) =
      (setupAndRootState state).getWord32
        (BitVec.ofNat 64 (0x22cb4 + 4 * index.val)) := by
  let copied := setupAndRootState state
  let pointers := parameterPointers copied
  have parameterRegs := parameterPointers_regs copied
  change (copyRootState pointers).getWord32 _ = copied.getWord32 _
  rw [copyParameter_data pointers parameterRegs.1 parameterRegs.2 index]
  change (parameterPointers copied).getWord32 _ = copied.getWord32 _
  simp only [MachineState.getWord32, parameterPointers_memory]

private theorem slots_mem_frame (state : MachineState) (address : Word)
    (outside : ∀ slot : Fin 4,
      address ≠ BitVec.ofNat 64 (0x43000 + 8 * slot.val)) :
    (SphincsVerifierSlots.headerState state).getMem address =
      state.getMem address := by
  simp only [SphincsVerifierSlots.headerState]
  rw [SphincsVerifierSlots.slot_memory 3,
    SphincsVerifierSlots.slot_memory 2,
    SphincsVerifierSlots.slot_memory 1,
    SphincsVerifierSlots.slot_memory 0]
  have o0 : address ≠ (274432#64) := by simpa using outside 0
  have o1 : address ≠ (274440#64) := by simpa using outside 1
  have o2 : address ≠ (274448#64) := by simpa using outside 2
  have o3 : address ≠ (274456#64) := by simpa using outside 3
  simp [o0, o1, o2, o3]

private theorem initial_slots_word_frame (state : MachineState)
    (address : Word)
    (outside : ∀ slot : Fin 4,
      alignToDword address ≠ BitVec.ofNat 64 (0x43000 + 8 * slot.val)) :
    (SphincsVerifierSlots.headerState
      (execInstrBr state (.JAL .x0 16))).getWord32 address =
      state.getWord32 address := by
  simp only [MachineState.getWord32]
  rw [slots_mem_frame _ _ outside]
  rfl

private theorem copied_root_preserves_parameter_source (state : MachineState)
    (destination : state.getReg .x7 = 0x40014) (index : Fin 5) :
    (copyRootState state).getWord32
      (BitVec.ofNat 64 (0x22cb4 + 4 * index.val)) =
      state.getWord32 (BitVec.ofNat 64 (0x22cb4 + 4 * index.val)) := by
  simp only [MachineState.getWord32]
  rw [copyRoot_mem_frame]
  intro offset
  fin_cases index <;> fin_cases offset <;>
    simp [destination, signExtend12, alignToDword]

theorem setupAndRoot_parameter_source (state : MachineState) (index : Fin 5) :
    (setupAndRootState state).getWord32
      (BitVec.ofNat 64 (0x22cb4 + 4 * index.val)) =
      state.getWord32 (BitVec.ofNat 64 (0x22cb4 + 4 * index.val)) := by
  let scratch := SphincsVerifierSlots.headerState
    (execInstrBr state (.JAL .x0 16))
  let pointers := addressSetupState scratch
  have destination := (addressSetup_regs scratch).2
  change (copyRootState pointers).getWord32 _ = state.getWord32 _
  rw [copied_root_preserves_parameter_source pointers destination index]
  have pointerFrame : pointers.getWord32
      (BitVec.ofNat 64 (0x22cb4 + 4 * index.val)) =
      scratch.getWord32 (BitVec.ofNat 64 (0x22cb4 + 4 * index.val)) := by
    simp only [MachineState.getWord32]
    rw [addressSetup_memory]
  rw [pointerFrame]
  apply initial_slots_word_frame
  intro slot
  fin_cases index <;> fin_cases slot <;>
    simp [alignToDword]

theorem setupAndBoth_root_source (state : MachineState) (index : Fin 5) :
    (setupAndBothState state).getWord32
      (BitVec.ofNat 64 (0x40014 + 4 * index.val)) =
      state.getWord32 (BitVec.ofNat 64 (0x22ca0 + 4 * index.val)) := by
  rw [setupAndBoth_root_word]
  have pointerFrame : (addressSetupState
      (SphincsVerifierSlots.headerState (execInstrBr state (.JAL .x0 16)))).getWord32
        (BitVec.ofNat 64 (0x22ca0 + 4 * index.val)) =
      (SphincsVerifierSlots.headerState
        (execInstrBr state (.JAL .x0 16))).getWord32
        (BitVec.ofNat 64 (0x22ca0 + 4 * index.val)) := by
    simp only [MachineState.getWord32]
    rw [addressSetup_memory]
  rw [pointerFrame]
  apply initial_slots_word_frame
  intro slot
  fin_cases index <;> fin_cases slot <;>
    simp [alignToDword]

theorem setupAndBoth_parameter_source (state : MachineState) (index : Fin 5) :
    (setupAndBothState state).getWord32
      (BitVec.ofNat 64 (0x40028 + 4 * index.val)) =
      state.getWord32 (BitVec.ofNat 64 (0x22cb4 + 4 * index.val)) := by
  rw [setupAndBoth_parameter_word]
  exact setupAndRoot_parameter_source state index

theorem firstHash_root_word (state : MachineState) (index : Fin 5) :
    (firstHashState state).getWord32
      (BitVec.ofNat 64 (0x40014 + 4 * index.val)) =
      state.getWord32 (BitVec.ofNat 64 (0x22ca0 + 4 * index.val)) := by
  rw [firstHash_root_frame, setupAndBoth_root_source]

theorem firstHash_parameter_word (state : MachineState) (index : Fin 5) :
    (firstHashState state).getWord32
      (BitVec.ofNat 64 (0x40028 + 4 * index.val)) =
      state.getWord32 (BitVec.ofNat 64 (0x22cb4 + 4 * index.val)) := by
  rw [firstHash_parameter_frame, setupAndBoth_parameter_source]

theorem firstHash_root_byte (state : MachineState) (index : Fin 5)
    (byte : Fin 4) :
    (firstHashState state).getByte
      (BitVec.ofNat 64 (0x40014 + 4 * index.val + byte.val)) =
      state.getByte
        (BitVec.ofNat 64 (0x22ca0 + 4 * index.val + byte.val)) := by
  rw [rootDestinationByte, rootSourceByte, firstHash_root_word]

theorem firstHash_parameter_byte (state : MachineState) (index : Fin 5)
    (byte : Fin 4) :
    (firstHashState state).getByte
      (BitVec.ofNat 64 (0x40028 + 4 * index.val + byte.val)) =
      state.getByte
        (BitVec.ofNat 64 (0x22cb4 + 4 * index.val + byte.val)) := by
  rw [parameterDestinationByte, parameterSourceByte, firstHash_parameter_word]

/-- info: 'SigGolfCandidate.SphincsVerifierHashBytes.firstHash_root_byte' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms firstHash_root_byte

/-- info: 'SigGolfCandidate.SphincsVerifierHashBytes.firstHash_parameter_byte' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms firstHash_parameter_byte

end SigGolfCandidate.SphincsVerifierHashBytes
