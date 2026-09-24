import SigGolfCandidate.SphincsBridge
import SigGolfCandidate.Execution
import SigGolfCandidate.SphincsImages

/-!
# Verifier's public-key commitment HASH site

The first oracle call in the exact verifier image occurs at 0x1130. Given the
prepared register and input-buffer invariant, the interpreter sends precisely
the scheme's 60-byte commitment input and charges one compression.
-/

namespace SigGolfCandidate.SphincsVerifierCommitment
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsBridge

theorem hash_site (state : MachineState) (pc : state.pc = 0x1130) :
    fetch SphincsImages.verify state = some (.base .ECALL) := by
  simp [fetch, pc, SphincsImages.verify_firstHashWord, decodeInstruction]

/-- Exact organizer interpreter step at the commitment query. -/
theorem hash_step (hash : Hash) (state : MachineState)
    (pk : SphincsSecurity.PublicKey) (ready : CommitmentReady state pk)
    (pc : state.pc = 0x1130) (steps : Nat) (result : Execution)
    (tail : Executes hash SphincsImages.verify
      (writeHash state (hash (toQuery (SphincsWire.commitmentInput pk)))) steps result) :
    Executes hash SphincsImages.verify state (steps + 1)
      (result.charge 8 1 1) := by
  have hquery := commitmentReady_hashInput state pk ready
  have hcost := (commitmentReady_hashCost state pk ready).2
  have htail : Executes hash SphincsImages.verify
      (writeHash state (hash (hashInput state))) steps result := by
    rw [hquery]
    exact tail
  have step := Executes.hash state steps result (hash_site state pc)
    ready.service (commitmentReady_hashCost state pk ready).1 htail
  simpa [hcost] using step

/-- info: 'SigGolfCandidate.SphincsVerifierCommitment.hash_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hash_step

end SigGolfCandidate.SphincsVerifierCommitment
