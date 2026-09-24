import SigGolfCandidate.SphincsVerifierCommitmentCheck

/-!
# Repeated 20-byte verifier copy block

The first operation after the commitment check copies the signature's
randomizer and internal root into the next hash input. Both copies use the
same five load/store pairs, at different code and memory addresses.
-/

namespace SigGolfCandidate.SphincsVerifierMessageCopy
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierCopy
open SigGolfCandidate.SphincsVerifierCommitmentCheck
open SigGolfCandidate.SphincsVerifierHashSetup
open SigGolfCandidate.SphincsVerifierLoader
open SigGolfCandidate.SphincsSubmission

theorem fetch_index (image : Image) (state : MachineState) (index : Nat)
    (small : 0x1000 + 4 * index < 2 ^ 64)
    (pc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * index)) :
    fetch image state = (image.code[index]?).bind decodeInstruction := by
  simp only [fetch, pc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
  have start : ¬ (0x1000 + 4 * index < 0x1000) := by omega
  have aligned : (0x1000 + 4 * index) % 4 = 0 := by omega
  have offset : (0x1000 + 4 * index - 0x1000) / 4 = index := by omega
  simp [start, aligned]

structure Copy20Code (image : Image) (start : Nat) : Prop where
  load : ∀ offset : Fin 5,
    (image.code[start + 2 * offset.val]?).bind decodeInstruction =
      some (.base (.LWU .x13 .x6 (4 * offset.val)))
  store : ∀ offset : Fin 5,
    (image.code[start + 2 * offset.val + 1]?).bind decodeInstruction =
      some (.base (.SW .x7 .x13 (4 * offset.val)))

theorem copy20_word_block (image : Image) (start : Nat)
    (code : Copy20Code image start) (offset : Fin 5)
    (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * (start + 2 * offset.val)))
    (source : state.getReg .x6 = 0x22cc8 ∨ state.getReg .x6 = 0x22ca0)
    (destination : state.getReg .x7 = 0x40028 ∨ state.getReg .x7 = 0x4003c)
    (small : 0x1000 + 4 * (start + 2 * offset.val + 1) < 2 ^ 64) :
    OrdinarySteps image state 2 (copyWordState offset state) := by
  let loaded := execInstrBr state (.LWU .x13 .x6 (4 * offset.val))
  let copied := execInstrBr loaded (.SW .x7 .x13 (4 * offset.val))
  have small0 : 0x1000 + 4 * (start + 2 * offset.val) < 2 ^ 64 := by omega
  have loadedPc : loaded.pc = BitVec.ofNat 64
      (0x1000 + 4 * (start + 2 * offset.val + 1)) := by
    simp only [loaded, execInstrBr, pc]
    change BitVec.ofNat 64 (0x1000 + 4 * (start + 2 * offset.val)) +
      BitVec.ofNat 64 4 = _
    rw [BitVec.ofNat_add_ofNat]
    congr 1
  apply OrdinarySteps.step state loaded _
    (.base (.LWU .x13 .x6 (4 * offset.val))) 1
  · rw [fetch_index image state _ small0 pc]
    exact code.load offset
  · rcases source with source | source <;>
      fin_cases offset <;>
      simp [loaded, ordinaryStep, memoryArgumentsValid, accessValid,
        rangeValid, signExtend12, source, MEMORY_BYTES]
  apply OrdinarySteps.step loaded copied _
    (.base (.SW .x7 .x13 (4 * offset.val))) 0
  · rw [fetch_index image loaded _ small loadedPc]
    exact code.store offset
  · have preserved : loaded.getReg .x7 = state.getReg .x7 := by
      simp [loaded, execInstrBr, MachineState.getReg_setReg_ne]
    rcases destination with destination | destination <;>
      fin_cases offset <;>
      simp [copied, ordinaryStep, memoryArgumentsValid, accessValid,
        rangeValid, signExtend12, preserved, destination, MEMORY_BYTES]
  exact OrdinarySteps.refl _

set_option maxHeartbeats 0 in
theorem first_copy_code : Copy20Code SphincsImages.verify 92 := by
  constructor <;> intro offset <;> fin_cases offset <;> decide

set_option maxHeartbeats 0 in
theorem second_copy_code : Copy20Code SphincsImages.verify 106 := by
  constructor <;> intro offset <;> fin_cases offset <;> decide

theorem copy20_word_pc (offset : Fin 5) (state : MachineState)
    (start : Nat)
    (pc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * (start + 2 * offset.val))) :
    (copyWordState offset state).pc =
      BitVec.ofNat 64 (0x1000 + 4 * (start + 2 * offset.val + 2)) := by
  have next : (copyWordState offset state).pc = state.pc + 8 := by
    simp [copyWordState, execInstrBr, BitVec.add_assoc]
  rw [next, pc]
  change BitVec.ofNat 64 (0x1000 + 4 * (start + 2 * offset.val)) +
    BitVec.ofNat 64 8 = _
  rw [BitVec.ofNat_add_ofNat]
  congr 1

set_option maxHeartbeats 0 in
theorem copy20_block (image : Image) (start : Nat)
    (code : Copy20Code image start) (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * start))
    (source : state.getReg .x6 = 0x22cc8 ∨ state.getReg .x6 = 0x22ca0)
    (destination : state.getReg .x7 = 0x40028 ∨ state.getReg .x7 = 0x4003c)
    (small : 0x1000 + 4 * (start + 10) < 2 ^ 64) :
    OrdinarySteps image state 10 (copyRootState state) := by
  let s1 := copyWordState 0 state
  let s2 := copyWordState 1 s1
  let s3 := copyWordState 2 s2
  let s4 := copyWordState 3 s3
  let s5 := copyWordState 4 s4
  have p0 : state.pc = BitVec.ofNat 64 (0x1000 + 4 * (start + 2 * (0 : Fin 5).val)) := by
    simpa using pc
  have p1 : s1.pc = BitVec.ofNat 64 (0x1000 + 4 * (start + 2 * (1 : Fin 5).val)) := by
    simpa using copy20_word_pc 0 state start p0
  have p2 : s2.pc = BitVec.ofNat 64 (0x1000 + 4 * (start + 2 * (2 : Fin 5).val)) := by
    simpa using copy20_word_pc 1 s1 start p1
  have p3 : s3.pc = BitVec.ofNat 64 (0x1000 + 4 * (start + 2 * (3 : Fin 5).val)) := by
    simpa using copy20_word_pc 2 s2 start p2
  have p4 : s4.pc = BitVec.ofNat 64 (0x1000 + 4 * (start + 2 * (4 : Fin 5).val)) := by
    simpa using copy20_word_pc 3 s3 start p3
  have source1 : s1.getReg .x6 = 0x22cc8 ∨ s1.getReg .x6 = 0x22ca0 := by
    rw [(copyWord_pointers 0 state).1]
    exact source
  have source2 : s2.getReg .x6 = 0x22cc8 ∨ s2.getReg .x6 = 0x22ca0 := by
    rw [(copyWord_pointers 1 s1).1]
    exact source1
  have source3 : s3.getReg .x6 = 0x22cc8 ∨ s3.getReg .x6 = 0x22ca0 := by
    rw [(copyWord_pointers 2 s2).1]
    exact source2
  have source4 : s4.getReg .x6 = 0x22cc8 ∨ s4.getReg .x6 = 0x22ca0 := by
    rw [(copyWord_pointers 3 s3).1]
    exact source3
  have destination1 : s1.getReg .x7 = 0x40028 ∨ s1.getReg .x7 = 0x4003c := by
    rw [(copyWord_pointers 0 state).2]
    exact destination
  have destination2 : s2.getReg .x7 = 0x40028 ∨ s2.getReg .x7 = 0x4003c := by
    rw [(copyWord_pointers 1 s1).2]
    exact destination1
  have destination3 : s3.getReg .x7 = 0x40028 ∨ s3.getReg .x7 = 0x4003c := by
    rw [(copyWord_pointers 2 s2).2]
    exact destination2
  have destination4 : s4.getReg .x7 = 0x40028 ∨ s4.getReg .x7 = 0x4003c := by
    rw [(copyWord_pointers 3 s3).2]
    exact destination3
  have b0 := copy20_word_block image start code 0 state p0 source destination
    (by omega)
  have b1 := copy20_word_block image start code 1 s1 p1 source1 destination1
    (by omega)
  have b2 := copy20_word_block image start code 2 s2 p2 source2 destination2
    (by omega)
  have b3 := copy20_word_block image start code 3 s3 p3 source3 destination3
    (by omega)
  have b4 := copy20_word_block image start code 4 s4 p4 source4 destination4
    (by omega)
  simpa [copyRootState, s1, s2, s3, s4, s5] using
    (((b0.append b1).append b2).append b3).append b4

def firstPointers (state : MachineState) : MachineState :=
  let state := execInstrBr state (.LUI .x6 0x23)
  let state := execInstrBr state (.ADDI .x6 .x6 (-824))
  let state := execInstrBr state (.LUI .x7 0x40)
  execInstrBr state (.ADDI .x7 .x7 40)

theorem firstPointers_regs (state : MachineState) :
    (firstPointers state).getReg .x6 = 0x22cc8 ∧
      (firstPointers state).getReg .x7 = 0x40028 := by
  simp [firstPointers, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem firstPointers_pc (state : MachineState) (pc : state.pc = 0x1160) :
    (firstPointers state).pc = 0x1170 := by
  simp [firstPointers, execInstrBr, pc]

theorem firstPointers_block (state : MachineState) (pc : state.pc = 0x1160) :
    OrdinarySteps SphincsImages.verify state 4 (firstPointers state) := by
  let s1 := execInstrBr state (.LUI .x6 0x23)
  let s2 := execInstrBr s1 (.ADDI .x6 .x6 (-824))
  let s3 := execInstrBr s2 (.LUI .x7 0x40)
  let s4 := execInstrBr s3 (.ADDI .x7 .x7 40)
  have p1 : s1.pc = 0x1164 := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x1168 := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x116c := by simp [s3, execInstrBr, p2]
  apply OrdinarySteps.step state s1 _ (.base (.LUI .x6 0x23)) 3
  · rw [fetch_index SphincsImages.verify state 88 (by decide) (by simpa using pc)]
    decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x6 .x6 (-824))) 2
  · rw [fetch_index SphincsImages.verify s1 89 (by decide) (by simpa using p1)]
    decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LUI .x7 0x40)) 1
  · rw [fetch_index SphincsImages.verify s2 90 (by decide) (by simpa using p2)]
    decide
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x7 .x7 40)) 0
  · rw [fetch_index SphincsImages.verify s3 91 (by decide) (by simpa using p3)]
    decide
  · rfl
  exact OrdinarySteps.refl _

def firstCopyState (state : MachineState) : MachineState :=
  copyRootState (firstPointers state)

theorem firstCopy_block (state : MachineState) (pc : state.pc = 0x1160) :
    OrdinarySteps SphincsImages.verify state 14 (firstCopyState state) := by
  have pointers := firstPointers_block state pc
  have copy := copy20_block SphincsImages.verify 92 first_copy_code
    (firstPointers state) (by simpa using firstPointers_pc state pc)
    (Or.inl (firstPointers_regs state).1)
    (Or.inl (firstPointers_regs state).2) (by decide)
  simpa [firstCopyState] using pointers.append copy

theorem copy20_final_pc (state : MachineState) (start : Nat)
    (pc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * start)) :
    (copyRootState state).pc = BitVec.ofNat 64 (0x1000 + 4 * (start + 10)) := by
  let s1 := copyWordState 0 state
  let s2 := copyWordState 1 s1
  let s3 := copyWordState 2 s2
  let s4 := copyWordState 3 s3
  have p1 : s1.pc = BitVec.ofNat 64 (0x1000 + 4 * (start + 2)) := by
    simpa using copy20_word_pc 0 state start (by simpa using pc)
  have p2 : s2.pc = BitVec.ofNat 64 (0x1000 + 4 * (start + 4)) := by
    simpa using copy20_word_pc 1 s1 start (by simpa using p1)
  have p3 : s3.pc = BitVec.ofNat 64 (0x1000 + 4 * (start + 6)) := by
    simpa using copy20_word_pc 2 s2 start (by simpa using p2)
  have p4 : s4.pc = BitVec.ofNat 64 (0x1000 + 4 * (start + 8)) := by
    simpa using copy20_word_pc 3 s3 start (by simpa using p3)
  simpa [copyRootState, s1, s2, s3, s4] using
    copy20_word_pc 4 s4 start (by simpa using p4)

theorem firstCopy_pc (state : MachineState) (pc : state.pc = 0x1160) :
    (firstCopyState state).pc = 0x1198 := by
  exact copy20_final_pc (firstPointers state) 92
    (by simpa using firstPointers_pc state pc)

def secondPointers (state : MachineState) : MachineState :=
  let state := execInstrBr state (.LUI .x6 0x23)
  let state := execInstrBr state (.ADDI .x6 .x6 (-864))
  let state := execInstrBr state (.LUI .x7 0x40)
  execInstrBr state (.ADDI .x7 .x7 60)

theorem secondPointers_regs (state : MachineState) :
    (secondPointers state).getReg .x6 = 0x22ca0 ∧
      (secondPointers state).getReg .x7 = 0x4003c := by
  simp [secondPointers, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem secondPointers_pc (state : MachineState) (pc : state.pc = 0x1198) :
    (secondPointers state).pc = 0x11a8 := by
  simp [secondPointers, execInstrBr, pc]

theorem secondPointers_block (state : MachineState) (pc : state.pc = 0x1198) :
    OrdinarySteps SphincsImages.verify state 4 (secondPointers state) := by
  let s1 := execInstrBr state (.LUI .x6 0x23)
  let s2 := execInstrBr s1 (.ADDI .x6 .x6 (-864))
  let s3 := execInstrBr s2 (.LUI .x7 0x40)
  let s4 := execInstrBr s3 (.ADDI .x7 .x7 60)
  have p1 : s1.pc = 0x119c := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x11a0 := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x11a4 := by simp [s3, execInstrBr, p2]
  apply OrdinarySteps.step state s1 _ (.base (.LUI .x6 0x23)) 3
  · rw [fetch_index SphincsImages.verify state 102 (by decide) (by simpa using pc)]
    decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x6 .x6 (-864))) 2
  · rw [fetch_index SphincsImages.verify s1 103 (by decide) (by simpa using p1)]
    decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LUI .x7 0x40)) 1
  · rw [fetch_index SphincsImages.verify s2 104 (by decide) (by simpa using p2)]
    decide
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x7 .x7 60)) 0
  · rw [fetch_index SphincsImages.verify s3 105 (by decide) (by simpa using p3)]
    decide
  · rfl
  exact OrdinarySteps.refl _

def bothCopiesState (state : MachineState) : MachineState :=
  copyRootState (secondPointers (firstCopyState state))

theorem bothCopies_block (state : MachineState) (pc : state.pc = 0x1160) :
    OrdinarySteps SphincsImages.verify state 28 (bothCopiesState state) := by
  have first := firstCopy_block state pc
  have afterFirstPc := firstCopy_pc state pc
  have pointers := secondPointers_block (firstCopyState state) afterFirstPc
  have afterSecondPointersPc := secondPointers_pc (firstCopyState state) afterFirstPc
  have copy := copy20_block SphincsImages.verify 106 second_copy_code
    (secondPointers (firstCopyState state))
    (by simpa using afterSecondPointersPc)
    (Or.inr (secondPointers_regs (firstCopyState state)).1)
    (Or.inr (secondPointers_regs (firstCopyState state)).2) (by decide)
  simpa [bothCopiesState] using (first.append pointers).append copy

theorem bothCopies_pc (state : MachineState) (pc : state.pc = 0x1160) :
    (bothCopiesState state).pc = 0x11d0 := by
  exact copy20_final_pc (secondPointers (firstCopyState state)) 106
    (by simpa using (secondPointers_pc (firstCopyState state)
      (firstCopy_pc state pc)))

def afterMessageCopiesState (state : MachineState) (answer : BitVec 256) :
    MachineState :=
  bothCopiesState (compareSuccessState (writeHash (firstHashState state) answer))

theorem loaded_messageCopies_block (publicKey : SigGolf.PublicKey)
    (message : Message) (witness : Bytes SphincsWire.signatureBytes)
    (state : MachineState) (answer : BitVec 256)
    (loaded : initialState submission .verify (message, publicKey, witness) = some state)
    (answerMatches : ∀ index : Fin 2,
      answer.extractLsb' (64 * index.val) 64 =
        publicKey.extractLsb' (64 * index.val) 64) :
    OrdinarySteps SphincsImages.verify (writeHash (firstHashState state) answer)
      37 (afterMessageCopiesState state answer) := by
  have compared := loaded_hashAnswer_compare_and_pc publicKey message witness
    state answer loaded answerMatches
  have copied := bothCopies_block _ compared.2
  simpa [afterMessageCopiesState] using compared.1.append copied

theorem loaded_messageCopies_pc (publicKey : SigGolf.PublicKey)
    (message : Message) (witness : Bytes SphincsWire.signatureBytes)
    (state : MachineState) (answer : BitVec 256)
    (loaded : initialState submission .verify (message, publicKey, witness) = some state)
    (answerMatches : ∀ index : Fin 2,
      answer.extractLsb' (64 * index.val) 64 =
        publicKey.extractLsb' (64 * index.val) 64) :
    (afterMessageCopiesState state answer).pc = 0x11d0 := by
  exact bothCopies_pc _
    (loaded_hashAnswer_compare_and_pc publicKey message witness state answer
      loaded answerMatches).2

theorem loaded_firstHash_messageCopies_executes (hash : Hash)
    (publicKey : SigGolf.PublicKey) (message : Message)
    (witness : Bytes SphincsWire.signatureBytes)
    (inner : SphincsSecurity.PublicKey) (state : MachineState)
    (loaded : initialState submission .verify (message, publicKey, witness) = some state)
    (encoded : EncodedWitness witness inner)
    (answerMatches : ∀ index : Fin 2,
      (hash (SigGolfCandidate.SphincsBridge.toQuery
        (SphincsWire.commitmentInput inner))).extractLsb'
          (64 * index.val) 64 =
        publicKey.extractLsb' (64 * index.val) 64)
    (steps : Nat) (result : Execution)
    (tail : Executes hash SphincsImages.verify
      (afterMessageCopiesState state
        (hash (SigGolfCandidate.SphincsBridge.toQuery
          (SphincsWire.commitmentInput inner)))) steps result) :
    Executes hash SphincsImages.verify state (((steps + 37) + 1) + 73)
      (((result.charge 37 0 0).charge 8 1 1).charge 73 0 0) := by
  have block := loaded_messageCopies_block publicKey message witness state
    (hash (SigGolfCandidate.SphincsBridge.toQuery
      (SphincsWire.commitmentInput inner))) loaded answerMatches
  exact loaded_firstHash_executes hash publicKey message witness inner state
    loaded encoded (steps + 37) (result.charge 37 0 0)
    (block.then_executes tail)

/-- info: 'SigGolfCandidate.SphincsVerifierMessageCopy.copy20_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms copy20_block

/-- info: 'SigGolfCandidate.SphincsVerifierMessageCopy.first_copy_code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms first_copy_code

/-- info: 'SigGolfCandidate.SphincsVerifierMessageCopy.second_copy_code' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms second_copy_code

/-- info: 'SigGolfCandidate.SphincsVerifierMessageCopy.bothCopies_block' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms bothCopies_block

/-- info: 'SigGolfCandidate.SphincsVerifierMessageCopy.loaded_firstHash_messageCopies_executes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms loaded_firstHash_messageCopies_executes

end SigGolfCandidate.SphincsVerifierMessageCopy
