import SigGolfCandidate.SphincsVerifierCopyParameter

/-!
# Parameter copy memory facts

The second five-word copy fills bytes 40–59 of the commitment input without
changing bytes 20–39 already copied from the witness root.
-/

namespace SigGolfCandidate.SphincsVerifierCopyParameterMemory
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierCopy
open SigGolfCandidate.SphincsVerifierCopyMemory

@[simp] private theorem getWord32_setPC (state : MachineState) (pc address : Word) :
    (state.setPC pc).getWord32 address = state.getWord32 address := rfl

@[simp] private theorem getWord32_setReg (state : MachineState) (reg : Reg)
    (value address : Word) :
    (state.setReg reg value).getWord32 address = state.getWord32 address := by
  simp [MachineState.getWord32]

private theorem parameterWord_data (offset : Fin 5) (state : MachineState)
    (source : state.getReg .x6 = 0x22cb4)
    (destination : state.getReg .x7 = 0x40028) :
    (copyWordState offset state).getWord32
      (BitVec.ofNat 64 (0x40028 + 4 * offset.val)) =
      state.getWord32 (BitVec.ofNat 64 (0x22cb4 + 4 * offset.val)) := by
  fin_cases offset <;>
    simp [copyWordState, execInstrBr, getWord32_setWord32_same,
      source, destination, signExtend12,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

private theorem parameterWord_other (written read : Fin 5)
    (different : written ≠ read) (state : MachineState)
    (destination : state.getReg .x7 = 0x40028) :
    (copyWordState written state).getWord32
      (BitVec.ofNat 64 (0x40028 + 4 * read.val)) =
      state.getWord32 (BitVec.ofNat 64 (0x40028 + 4 * read.val)) := by
  fin_cases written <;> fin_cases read <;>
    simp_all [copyWordState, execInstrBr,
      signExtend12, MachineState.getReg_setReg_ne] <;>
    (rw [getWord32_setWord32_other _ _ _ _ (by decide)]; simp)

private theorem parameterWord_source (written read : Fin 5)
    (state : MachineState) (destination : state.getReg .x7 = 0x40028) :
    (copyWordState written state).getWord32
      (BitVec.ofNat 64 (0x22cb4 + 4 * read.val)) =
      state.getWord32 (BitVec.ofNat 64 (0x22cb4 + 4 * read.val)) := by
  fin_cases written <;> fin_cases read <;>
    simp_all [copyWordState, execInstrBr,
      signExtend12, MachineState.getReg_setReg_ne] <;>
    (rw [getWord32_setWord32_other _ _ _ _ (by decide)]; simp)

private def ParameterInvariant (original : MachineState) (count : Nat)
    (state : MachineState) : Prop :=
  state.getReg .x6 = 0x22cb4 ∧
  state.getReg .x7 = 0x40028 ∧
  (∀ index : Fin 5,
    state.getWord32 (BitVec.ofNat 64 (0x22cb4 + 4 * index.val)) =
      original.getWord32 (BitVec.ofNat 64 (0x22cb4 + 4 * index.val))) ∧
  (∀ index : Fin 5, index.val < count →
    state.getWord32 (BitVec.ofNat 64 (0x40028 + 4 * index.val)) =
      original.getWord32 (BitVec.ofNat 64 (0x22cb4 + 4 * index.val)))

private theorem parameterStep (original state : MachineState) (slot : Fin 5)
    (invariant : ParameterInvariant original slot.val state) :
    ParameterInvariant original (slot.val + 1) (copyWordState slot state) := by
  rcases invariant with ⟨source, destination, sourceWords, copiedWords⟩
  obtain ⟨sourceAfter, destinationAfter⟩ := copyWord_pointers slot state
  refine ⟨sourceAfter.trans source, destinationAfter.trans destination, ?_, ?_⟩
  · intro index
    rw [parameterWord_source slot index state destination]
    exact sourceWords index
  · intro index before
    by_cases same : slot = index
    · subst index
      rw [parameterWord_data slot state source destination]
      exact sourceWords slot
    · rw [parameterWord_other slot index same state destination]
      have smaller : index.val < slot.val := by
        have unequal : slot.val ≠ index.val := fun h => same (Fin.ext h)
        omega
      exact copiedWords index smaller

theorem copyParameter_data (original : MachineState)
    (source : original.getReg .x6 = 0x22cb4)
    (destination : original.getReg .x7 = 0x40028)
    (index : Fin 5) :
    (copyRootState original).getWord32
      (BitVec.ofNat 64 (0x40028 + 4 * index.val)) =
      original.getWord32 (BitVec.ofNat 64 (0x22cb4 + 4 * index.val)) := by
  have initial : ParameterInvariant original 0 original := by
    refine ⟨source, destination, fun _ => rfl, ?_⟩
    intro index impossible
    omega
  have after0 := parameterStep original original 0 initial
  have after1 := parameterStep original (copyWordState 0 original) 1 after0
  have after2 := parameterStep original (copyWordState 1 (copyWordState 0 original))
    2 after1
  have after3 := parameterStep original
    (copyWordState 2 (copyWordState 1 (copyWordState 0 original))) 3 after2
  have after4 := parameterStep original
    (copyWordState 3 (copyWordState 2 (copyWordState 1 (copyWordState 0 original))))
    4 after3
  exact after4.2.2.2 index (by omega)

private theorem parameterWord_preserves_root (written root : Fin 5)
    (state : MachineState) (destination : state.getReg .x7 = 0x40028) :
    (copyWordState written state).getWord32
      (BitVec.ofNat 64 (0x40014 + 4 * root.val)) =
      state.getWord32 (BitVec.ofNat 64 (0x40014 + 4 * root.val)) := by
  fin_cases written <;> fin_cases root <;>
    simp_all [copyWordState, execInstrBr,
      signExtend12, MachineState.getReg_setReg_ne] <;>
    (rw [getWord32_setWord32_other _ _ _ _ (by decide)]; simp)

theorem copyParameter_preserves_root (state : MachineState)
    (destination : state.getReg .x7 = 0x40028) (root : Fin 5) :
    (copyRootState state).getWord32
      (BitVec.ofNat 64 (0x40014 + 4 * root.val)) =
      state.getWord32 (BitVec.ofNat 64 (0x40014 + 4 * root.val)) := by
  have h1 : (copyWordState 0 state).getReg .x7 = 0x40028 :=
    (copyWord_pointers 0 state).2.trans destination
  have h2 : (copyWordState 1 (copyWordState 0 state)).getReg .x7 = 0x40028 :=
    (copyWord_pointers 1 _).2.trans h1
  have h3 : (copyWordState 2 (copyWordState 1 (copyWordState 0 state))).getReg .x7 =
      0x40028 := (copyWord_pointers 2 _).2.trans h2
  have h4 : (copyWordState 3 (copyWordState 2
      (copyWordState 1 (copyWordState 0 state)))).getReg .x7 = 0x40028 :=
    (copyWord_pointers 3 _).2.trans h3
  simp only [copyRootState]
  rw [parameterWord_preserves_root 4 root _ h4,
    parameterWord_preserves_root 3 root _ h3,
    parameterWord_preserves_root 2 root _ h2,
    parameterWord_preserves_root 1 root _ h1,
    parameterWord_preserves_root 0 root _ destination]

/-- info: 'SigGolfCandidate.SphincsVerifierCopyParameterMemory.copyParameter_data' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms copyParameter_data

end SigGolfCandidate.SphincsVerifierCopyParameterMemory
