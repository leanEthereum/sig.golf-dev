import SigGolfCandidate.SphincsVerifierCopy
import RiscvZkvm.Rv64.Logic.WordOps

/-!
# Commitment copy memory facts

The verifier copies two 20-byte witness fields into the commitment hash
buffer with 32-bit loads and stores. These lemmas relate the actual memory
effects to the bytes in the submitted witness.
-/

namespace SigGolfCandidate.SphincsVerifierCopyMemory
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierCopy

@[simp] private theorem getWord32_setPC (state : MachineState) (pc address : Word) :
    (state.setPC pc).getWord32 address = state.getWord32 address := rfl

@[simp] private theorem getWord32_setReg (state : MachineState) (reg : Reg)
    (value address : Word) :
    (state.setReg reg value).getWord32 address = state.getWord32 address := by
  simp [MachineState.getWord32]

theorem getWord32_setWord32_same (state : MachineState) (address : Word)
    (value : BitVec 32) :
    (state.setWord32 address value).getWord32 address = value := by
  rw [getWord32_eq, setWord32_eq, MachineState.getMem_setMem_eq]
  exact extractWord32_replaceWord32_same (state.getMem (alignToDword address))
    ⟨(byteOffset address) / 4, by have := byteOffset_lt_8 (addr := address); omega⟩ value

private theorem extractWord32_replaceWord32_other0 (word : Word) (value : BitVec 32) :
    extractWord32 (replaceWord32 word 0 value) 1 = extractWord32 word 1 := by
  simp only [extractWord32, replaceWord32]
  ext i (hi : i < 32)
  simp [BitVec.truncate, BitVec.zeroExtend]
  try { nat_lt_cases i 32 <;> simp_all }

private theorem extractWord32_replaceWord32_other1 (word : Word) (value : BitVec 32) :
    extractWord32 (replaceWord32 word 1 value) 0 = extractWord32 word 0 := by
  simp only [extractWord32, replaceWord32]
  ext i (hi : i < 32)
  simp [BitVec.truncate, BitVec.zeroExtend]
  try { nat_lt_cases i 32 <;> simp_all }

/-- A 32-bit store leaves every other 32-bit lane unchanged, even in the same cell. -/
theorem getWord32_setWord32_other (state : MachineState) (written read : Word)
    (value : BitVec 32)
    (other : alignToDword written ≠ alignToDword read ∨
      byteOffset written / 4 ≠ byteOffset read / 4) :
    (state.setWord32 written value).getWord32 read = state.getWord32 read := by
  rw [getWord32_eq, setWord32_eq]
  by_cases hcell : alignToDword read = alignToDword written
  · rw [hcell, MachineState.getMem_setMem_eq]
    have hpos : byteOffset written / 4 ≠ byteOffset read / 4 := by
      rcases other with h | h
      · exact False.elim (h hcell.symm)
      · exact h
    have hw : byteOffset written / 4 < 2 := by
      have := byteOffset_lt_8 (addr := written)
      omega
    have hr : byteOffset read / 4 < 2 := by
      have := byteOffset_lt_8 (addr := read)
      omega
    interval_cases hp : byteOffset written / 4 <;>
      interval_cases hq : byteOffset read / 4 <;>
      simp_all [extractWord32_replaceWord32_other0,
        extractWord32_replaceWord32_other1, MachineState.getWord32]
    all_goals
      have hz : byteOffset read / 4 = 0 := by omega
      simp [hz]
  · rw [MachineState.getMem_setMem_ne hcell]
    rfl

/-- Each verifier load/store pair writes the corresponding source word. -/
theorem copyWord_data (offset : Fin 5) (state : MachineState)
    (source : state.getReg .x6 = 0x22ca0)
    (destination : state.getReg .x7 = 0x40014) :
    (copyWordState offset state).getWord32
      (BitVec.ofNat 64 (0x40014 + 4 * offset.val)) =
      state.getWord32 (BitVec.ofNat 64 (0x22ca0 + 4 * offset.val)) := by
  fin_cases offset <;>
    simp [copyWordState, execInstrBr, getWord32_setWord32_same,
      source, destination, signExtend12,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem copyWord_other (written read : Fin 5) (different : written ≠ read)
    (state : MachineState) (destination : state.getReg .x7 = 0x40014) :
    (copyWordState written state).getWord32
      (BitVec.ofNat 64 (0x40014 + 4 * read.val)) =
      state.getWord32 (BitVec.ofNat 64 (0x40014 + 4 * read.val)) := by
  fin_cases written <;> fin_cases read <;>
    simp_all [copyWordState, execInstrBr,
      signExtend12, MachineState.getReg_setReg_ne] <;>
    (rw [getWord32_setWord32_other _ _ _ _ (by decide)]; simp)

/-- Stores into the hash buffer do not modify any source word in the witness. -/
theorem copyWord_source (written read : Fin 5) (state : MachineState)
    (destination : state.getReg .x7 = 0x40014) :
    (copyWordState written state).getWord32
      (BitVec.ofNat 64 (0x22ca0 + 4 * read.val)) =
      state.getWord32 (BitVec.ofNat 64 (0x22ca0 + 4 * read.val)) := by
  fin_cases written <;> fin_cases read <;>
    simp_all [copyWordState, execInstrBr,
      signExtend12, MachineState.getReg_setReg_ne] <;>
    (rw [getWord32_setWord32_other _ _ _ _ (by decide)]; simp)

private def CopyInvariant (original : MachineState) (count : Nat)
    (state : MachineState) : Prop :=
  state.getReg .x6 = 0x22ca0 ∧
  state.getReg .x7 = 0x40014 ∧
  (∀ index : Fin 5,
    state.getWord32 (BitVec.ofNat 64 (0x22ca0 + 4 * index.val)) =
      original.getWord32 (BitVec.ofNat 64 (0x22ca0 + 4 * index.val))) ∧
  (∀ index : Fin 5, index.val < count →
    state.getWord32 (BitVec.ofNat 64 (0x40014 + 4 * index.val)) =
      original.getWord32 (BitVec.ofNat 64 (0x22ca0 + 4 * index.val)))

private theorem copyStep (original state : MachineState) (slot : Fin 5)
    (invariant : CopyInvariant original slot.val state) :
    CopyInvariant original (slot.val + 1) (copyWordState slot state) := by
  rcases invariant with ⟨source, destination, sourceWords, copiedWords⟩
  obtain ⟨sourceAfter, destinationAfter⟩ := copyWord_pointers slot state
  refine ⟨sourceAfter.trans source, destinationAfter.trans destination, ?_, ?_⟩
  · intro index
    rw [copyWord_source slot index state destination]
    exact sourceWords index
  · intro index before
    by_cases same : slot = index
    · subst index
      rw [copyWord_data slot state source destination]
      exact sourceWords slot
    · rw [copyWord_other slot index same state destination]
      have smaller : index.val < slot.val := by
        have unequal : slot.val ≠ index.val := fun h => same (Fin.ext h)
        omega
      exact copiedWords index smaller

theorem copyRoot_data (original : MachineState)
    (source : original.getReg .x6 = 0x22ca0)
    (destination : original.getReg .x7 = 0x40014)
    (index : Fin 5) :
    (copyRootState original).getWord32
      (BitVec.ofNat 64 (0x40014 + 4 * index.val)) =
      original.getWord32 (BitVec.ofNat 64 (0x22ca0 + 4 * index.val)) := by
  have initial : CopyInvariant original 0 original := by
    refine ⟨source, destination, fun _ => rfl, ?_⟩
    intro index impossible
    omega
  have after0 := copyStep original original 0 initial
  have after1 := copyStep original (copyWordState 0 original) 1 after0
  have after2 := copyStep original (copyWordState 1 (copyWordState 0 original)) 2 after1
  have after3 := copyStep original
    (copyWordState 2 (copyWordState 1 (copyWordState 0 original))) 3 after2
  have after4 := copyStep original
    (copyWordState 3 (copyWordState 2 (copyWordState 1 (copyWordState 0 original))))
    4 after3
  exact after4.2.2.2 index (by omega)

/-- info: 'SigGolfCandidate.SphincsVerifierCopyMemory.copyRoot_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms copyRoot_data

end SigGolfCandidate.SphincsVerifierCopyMemory
