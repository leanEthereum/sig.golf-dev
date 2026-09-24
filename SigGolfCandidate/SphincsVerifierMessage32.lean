import SigGolfCandidate.SphincsVerifierMessageCopy
import SigGolfCandidate.SphincsExpansion

/-!
# Thirty-two-byte message copy

The verifier copies the 32-byte message into the next HASH input with four
iterations of the same six-instruction loop used by the expand image.
-/

namespace SigGolfCandidate.SphincsVerifierMessage32
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierMessageCopy
open SigGolfCandidate.Sphincs.Expansion
open SigGolfCandidate.SphincsVerifierHashSetup
open SigGolfCandidate.SphincsVerifierLoader
open SigGolfCandidate.SphincsSubmission

def prefixState (state : MachineState) : MachineState :=
  let state := execInstrBr state (.ADDI .x6 .x0 0)
  let state := execInstrBr state (.LUI .x7 0x40)
  let state := execInstrBr state (.ADDI .x7 .x7 80)
  execInstrBr state (.ADDI .x10 .x0 4)

theorem prefix_regs (state : MachineState) :
    (prefixState state).getReg .x6 = 0 ∧
      (prefixState state).getReg .x7 = 0x40050 ∧
      (prefixState state).getReg .x10 = 4 := by
  simp [prefixState, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem prefix_pc (state : MachineState) (pc : state.pc = 0x11d0) :
    (prefixState state).pc = 0x11e0 := by
  simp [prefixState, execInstrBr, pc]

theorem prefix_block (state : MachineState) (pc : state.pc = 0x11d0) :
    OrdinarySteps SphincsImages.verify state 4 (prefixState state) := by
  let s1 := execInstrBr state (.ADDI .x6 .x0 0)
  let s2 := execInstrBr s1 (.LUI .x7 0x40)
  let s3 := execInstrBr s2 (.ADDI .x7 .x7 80)
  let s4 := execInstrBr s3 (.ADDI .x10 .x0 4)
  have p1 : s1.pc = 0x11d4 := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x11d8 := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x11dc := by simp [s3, execInstrBr, p2]
  apply OrdinarySteps.step state s1 _ (.base (.ADDI .x6 .x0 0)) 3
  · rw [fetch_index SphincsImages.verify state 116 (by decide) (by simpa using pc)]
    decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x7 0x40)) 2
  · rw [fetch_index SphincsImages.verify s1 117 (by decide) (by simpa using p1)]
    decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x7 .x7 80)) 1
  · rw [fetch_index SphincsImages.verify s2 118 (by decide) (by simpa using p2)]
    decide
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x10 .x0 4)) 0
  · rw [fetch_index SphincsImages.verify s3 119 (by decide) (by simpa using p3)]
    decide
  · rfl
  exact OrdinarySteps.refl _

theorem loop_block (state : MachineState) (pc : state.pc = 0x11e0)
    (src : accessValid (state.getReg .x6) 8 = true)
    (dst : accessValid (state.getReg .x7) 8 = true) :
    OrdinarySteps SphincsImages.verify state 6 (loopNext state) := by
  let s1 := execInstrBr state (.LD .x11 .x6 0)
  let s2 := execInstrBr s1 (.SD .x7 .x11 0)
  let s3 := execInstrBr s2 (.ADDI .x6 .x6 8)
  let s4 := execInstrBr s3 (.ADDI .x7 .x7 8)
  let s5 := execInstrBr s4 (.ADDI .x10 .x10 (-1))
  let s6 := execInstrBr s5 (.BNE .x10 .x0 (-20))
  have p1 : s1.pc = 0x11e4 := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x11e8 := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x11ec := by simp [s3, execInstrBr, p2]
  have p4 : s4.pc = 0x11f0 := by simp [s4, execInstrBr, p3]
  have p5 : s5.pc = 0x11f4 := by simp [s5, execInstrBr, p4]
  apply OrdinarySteps.step state s1 _ (.base (.LD .x11 .x6 0)) 5
  · rw [fetch_index SphincsImages.verify state 120 (by decide) (by simpa using pc)]
    decide
  · simp [s1, ordinaryStep, memoryArgumentsValid, signExtend12, src]
  apply OrdinarySteps.step s1 s2 _ (.base (.SD .x7 .x11 0)) 4
  · rw [fetch_index SphincsImages.verify s1 121 (by decide) (by simpa using p1)]
    decide
  · have dst1 : accessValid (s1.getReg .x7) 8 = true := by
      simpa [s1, execInstrBr, MachineState.getReg_setReg_ne] using dst
    simp [s2, ordinaryStep, memoryArgumentsValid, signExtend12, dst1]
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x6 .x6 8)) 3
  · rw [fetch_index SphincsImages.verify s2 122 (by decide) (by simpa using p2)]
    decide
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x7 .x7 8)) 2
  · rw [fetch_index SphincsImages.verify s3 123 (by decide) (by simpa using p3)]
    decide
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x10 .x10 (-1))) 1
  · rw [fetch_index SphincsImages.verify s4 124 (by decide) (by simpa using p4)]
    decide
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.BNE .x10 .x0 (-20))) 0
  · rw [fetch_index SphincsImages.verify s5 125 (by decide) (by simpa using p5)]
    decide
  · rfl
  exact OrdinarySteps.refl _

theorem loop_next_pc (state : MachineState) (pc : state.pc = 0x11e0) :
    (loopNext state).pc =
      if state.getReg .x10 = 1 then 0x11f8 else 0x11e0 := by
  have decrement (x : BitVec 64) : x - 1#64 = 0#64 ↔ x = 1#64 := by
    exact BitVec.sub_left_inj (x := x) (y := 1) 1
  simp only [loopNext, execInstrBr, pc_ite, pc_setPC,
    loop_body_pc, loop_body_count, reg_zero, pc]
  simp only [signExtend13]
  simp
  simp only [decrement]

def LoopInvariant (remaining : Nat) (state : MachineState) : Prop :=
  remaining ≤ 4 ∧
    state.pc = (if remaining = 0 then 0x11f8 else 0x11e0) ∧
    state.getReg .x6 = BitVec.ofNat 64 (8 * (4 - remaining)) ∧
    state.getReg .x7 = BitVec.ofNat 64 (0x40050 + 8 * (4 - remaining)) ∧
    state.getReg .x10 = BitVec.ofNat 64 remaining

theorem loop_invariant (remaining : Nat) (state : MachineState)
    (inv : LoopInvariant (remaining + 1) state) :
    LoopInvariant remaining (loopNext state) := by
  obtain ⟨bound, pc, source, destination, count⟩ := inv
  have pc0 : state.pc = 0x11e0 := by simpa using pc
  have zeroAfter : BitVec.ofNat 64 (remaining + 1) = 1 ↔ remaining = 0 := by
    have small : remaining + 1 < 2 ^ 64 := by omega
    constructor
    · intro h
      have value := congrArg BitVec.toNat h
      change (remaining + 1) % 2 ^ 64 = 1 at value
      rw [Nat.mod_eq_of_lt small] at value
      omega
    · intro h
      subst remaining
      rfl
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩
  · rw [loop_next_pc state pc0, count]
    simp only [zeroAfter]
  · rw [(loop_next_regs state).1, source]
    change BitVec.ofNat 64 (8 * (4 - (remaining + 1))) +
      BitVec.ofNat 64 8 = _
    rw [← BitVec.ofNat_add]
    congr 1
    omega
  · rw [(loop_next_regs state).2.1, destination]
    change BitVec.ofNat 64 (0x40050 + 8 * (4 - (remaining + 1))) +
      BitVec.ofNat 64 8 = _
    rw [← BitVec.ofNat_add]
    congr 1
    omega
  · rw [(loop_next_regs state).2.2, count, BitVec.ofNat_add]
    exact BitVec.add_sub_cancel _ _

theorem loop_accesses (remaining : Nat) (state : MachineState)
    (inv : LoopInvariant (remaining + 1) state) :
    accessValid (state.getReg .x6) 8 = true ∧
      accessValid (state.getReg .x7) 8 = true := by
  obtain ⟨bound, _, source, destination, _⟩ := inv
  simp [accessValid, rangeValid, source, destination,
    BitVec.toNat_ofNat, MEMORY_BYTES, Nat.add_mod, Nat.mul_mod]
  omega

theorem loop_run (remaining : Nat) (state : MachineState)
    (inv : LoopInvariant remaining state) :
    ∃ final, OrdinarySteps SphincsImages.verify state (6 * remaining) final ∧
      LoopInvariant 0 final := by
  induction remaining generalizing state with
  | zero =>
    exact ⟨state, by simpa using OrdinarySteps.refl state, inv⟩
  | succ remaining ih =>
    have pc : state.pc = 0x11e0 := by simpa [LoopInvariant] using inv.2.1
    have access := loop_accesses remaining state inv
    have first := loop_block state pc access.1 access.2
    have next := loop_invariant remaining state inv
    obtain ⟨final, rest, finalInv⟩ := ih (loopNext state) next
    refine ⟨final, ?_, finalInv⟩
    simpa [Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using first.append rest

theorem prefix_invariant (state : MachineState) (pc : state.pc = 0x11d0) :
    LoopInvariant 4 (prefixState state) := by
  refine ⟨by decide, by simpa using prefix_pc state pc,
    (prefix_regs state).1, (prefix_regs state).2.1,
    (prefix_regs state).2.2⟩

theorem message32_block (state : MachineState) (pc : state.pc = 0x11d0) :
    ∃ final, OrdinarySteps SphincsImages.verify state 28 final ∧
      LoopInvariant 0 final := by
  have prefixTrace := prefix_block state pc
  obtain ⟨final, copied, invariant⟩ :=
    loop_run 4 (prefixState state) (prefix_invariant state pc)
  refine ⟨final, ?_, invariant⟩
  simpa using prefixTrace.append copied

theorem loaded_message32_block (publicKey : SigGolf.PublicKey)
    (message : Message) (witness : Bytes SphincsWire.signatureBytes)
    (state : MachineState) (answer : BitVec 256)
    (loaded : initialState submission .verify (message, publicKey, witness) = some state)
    (answerMatches : ∀ index : Fin 2,
      answer.extractLsb' (64 * index.val) 64 =
        publicKey.extractLsb' (64 * index.val) 64) :
    ∃ final, OrdinarySteps SphincsImages.verify
      (writeHash (firstHashState state) answer) 65 final ∧
      LoopInvariant 0 final := by
  have copies := loaded_messageCopies_block publicKey message witness state
    answer loaded answerMatches
  have copiesPc := loaded_messageCopies_pc publicKey message witness state
    answer loaded answerMatches
  obtain ⟨final, messageCopy, invariant⟩ :=
    message32_block (afterMessageCopiesState state answer) copiesPc
  refine ⟨final, ?_, invariant⟩
  simpa using copies.append messageCopy

/-- info: 'SigGolfCandidate.SphincsVerifierMessage32.loop_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms loop_block

/-- info: 'SigGolfCandidate.SphincsVerifierMessage32.loop_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms loop_run

/-- info: 'SigGolfCandidate.SphincsVerifierMessage32.loaded_message32_block' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms loaded_message32_block

end SigGolfCandidate.SphincsVerifierMessage32
