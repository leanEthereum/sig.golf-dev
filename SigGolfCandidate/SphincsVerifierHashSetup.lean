import SigGolfCandidate.SphincsVerifierHeader

/-!
# First verifier HASH call setup

After the commitment header, six ordinary instructions select the 60-byte
hash buffer, 480-bit input length, answer buffer, and HASH service.
-/

namespace SigGolfCandidate.SphincsVerifierHashSetup
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierPrefix
open SigGolfCandidate.SphincsVerifierHeader
open SigGolfCandidate.SphincsVerifierCopyParameter

def hashRegistersState (state : MachineState) : MachineState :=
  let state := execInstrBr state (.LUI .x10 0x40)
  let state := execInstrBr state (.ADDI .x10 .x10 0)
  let state := execInstrBr state (.ADDI .x11 .x0 480)
  let state := execInstrBr state (.LUI .x12 0x42)
  let state := execInstrBr state (.ADDI .x12 .x12 0)
  execInstrBr state (.ADDI .x5 .x0 1)

theorem hashRegisters_block (state : MachineState) (pc : state.pc = 0x1118) :
    OrdinarySteps SphincsImages.verify state 6 (hashRegistersState state) := by
  let s1 := execInstrBr state (.LUI .x10 0x40)
  let s2 := execInstrBr s1 (.ADDI .x10 .x10 0)
  let s3 := execInstrBr s2 (.ADDI .x11 .x0 480)
  let s4 := execInstrBr s3 (.LUI .x12 0x42)
  let s5 := execInstrBr s4 (.ADDI .x12 .x12 0)
  let s6 := execInstrBr s5 (.ADDI .x5 .x0 1)
  have p1 : s1.pc = 0x111c := by simp [s1, execInstrBr, MachineState.setPC, pc]
  have p2 : s2.pc = 0x1120 := by simp [s2, execInstrBr, MachineState.setPC, p1]
  have p3 : s3.pc = 0x1124 := by simp [s3, execInstrBr, MachineState.setPC, p2]
  have p4 : s4.pc = 0x1128 := by simp [s4, execInstrBr, MachineState.setPC, p3]
  have p5 : s5.pc = 0x112c := by simp [s5, execInstrBr, MachineState.setPC, p4]
  apply OrdinarySteps.step state s1 _ (.base (.LUI .x10 0x40)) 5
  · rw [fetch_at state 70 (by decide) (by simpa using pc)]; decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x10 .x10 0)) 4
  · rw [fetch_at s1 71 (by decide) (by simpa using p1)]; decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x11 .x0 480)) 3
  · rw [fetch_at s2 72 (by decide) (by simpa using p2)]; decide
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.LUI .x12 0x42)) 2
  · rw [fetch_at s3 73 (by decide) (by simpa using p3)]; decide
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x12 .x12 0)) 1
  · rw [fetch_at s4 74 (by decide) (by simpa using p4)]; decide
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADDI .x5 .x0 1)) 0
  · rw [fetch_at s5 75 (by decide) (by simpa using p5)]; decide
  · rfl
  exact OrdinarySteps.refl _

theorem hashRegisters_pc (state : MachineState) (pc : state.pc = 0x1118) :
    (hashRegistersState state).pc = 0x1130 := by
  simp [hashRegistersState, execInstrBr, MachineState.setPC, pc]

theorem hashRegisters_ready (state : MachineState) :
    (hashRegistersState state).getReg .x10 = 0x40000 ∧
    (hashRegistersState state).getReg .x11 = 480 ∧
    (hashRegistersState state).getReg .x12 = 0x42000 ∧
    (hashRegistersState state).getReg .x5 = 1 := by
  simp [hashRegistersState, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem hashRegisters_memory (state : MachineState) (address : Word) :
    (hashRegistersState state).getMem address = state.getMem address := by
  simp [hashRegistersState, execInstrBr]

def hashSetupState (state : MachineState) : MachineState :=
  hashRegistersState (headerState state)

theorem hashSetup_block (state : MachineState) (pc : state.pc = 0x10c0) :
    OrdinarySteps SphincsImages.verify state 28 (hashSetupState state) := by
  have header := header_block state pc
  have headerPc := header_next_pc state pc
  have registers := hashRegisters_block (headerState state) headerPc
  simpa [hashSetupState] using header.append registers

theorem hashSetup_pc (state : MachineState) (pc : state.pc = 0x10c0) :
    (hashSetupState state).pc = 0x1130 :=
  hashRegisters_pc (headerState state) (header_next_pc state pc)

def firstHashState (state : MachineState) : MachineState :=
  hashSetupState (setupAndBothState state)

theorem firstHash_block (state : MachineState) (pc : state.pc = 0x1000) :
    OrdinarySteps SphincsImages.verify state 73 (firstHashState state) := by
  have copies := setupAndBoth_block state pc
  have copiesPc := setupAndBoth_pc state pc
  have header := hashSetup_block (setupAndBothState state) copiesPc
  simpa [firstHashState] using copies.append header

theorem firstHash_pc (state : MachineState) (pc : state.pc = 0x1000) :
    (firstHashState state).pc = 0x1130 :=
  hashSetup_pc (setupAndBothState state) (setupAndBoth_pc state pc)

theorem firstHash_registers (state : MachineState) :
    (firstHashState state).getReg .x10 = 0x40000 ∧
    (firstHashState state).getReg .x11 = 480 ∧
    (firstHashState state).getReg .x12 = 0x42000 ∧
    (firstHashState state).getReg .x5 = 1 :=
  hashRegisters_ready (headerState (setupAndBothState state))

/-- The whole entry-to-HASH trace, conditional only on the prepared input bytes. -/
theorem firstHash_executes (hash : Hash) (state : MachineState)
    (publicKey : SphincsSecurity.PublicKey)
    (pc : state.pc = 0x1000)
    (ready : SigGolfCandidate.SphincsBridge.CommitmentReady
      (firstHashState state) publicKey)
    (steps : Nat) (result : Execution)
    (tail : Executes hash SphincsImages.verify
      (writeHash (firstHashState state)
        (hash (SigGolfCandidate.SphincsBridge.toQuery
          (SigGolfCandidate.SphincsWire.commitmentInput publicKey)))) steps result) :
    Executes hash SphincsImages.verify state ((steps + 1) + 73)
      ((result.charge 8 1 1).charge 73 0 0) := by
  have hashStep := SphincsVerifierCommitment.hash_step hash (firstHashState state)
    publicKey ready (firstHash_pc state pc) steps result tail
  exact (firstHash_block state pc).then_executes hashStep

/-- info: 'SigGolfCandidate.SphincsVerifierHashSetup.hashSetup_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hashSetup_block

/-- info: 'SigGolfCandidate.SphincsVerifierHashSetup.firstHash_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms firstHash_block

/-- info: 'SigGolfCandidate.SphincsVerifierHashSetup.firstHash_executes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms firstHash_executes

end SigGolfCandidate.SphincsVerifierHashSetup
