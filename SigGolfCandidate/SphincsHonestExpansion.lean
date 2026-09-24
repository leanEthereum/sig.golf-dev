import SigGolfCandidate.SphincsExpandCopy

namespace SigGolfCandidate.Sphincs
open SigGolf OracleComp

/-- Exact organizer result for the candidate's expansion program. -/
theorem expand_exact (hash : Hash) (message : Message) (pk : PublicKey)
    (signature : Bytes SphincsWire.signatureBytes) :
    SphincsSubmission.submission.runWith hash .expand (message, pk, signature) =
      ⟨some signature, true, 8500, 0, 0⟩ := by
  have value := Expansion.run_identity hash (message, pk, signature)
  obtain ⟨finished, _, cycles, calls, blocks⟩ :=
    Expansion.run_bound hash (message, pk, signature)
  cases h : SphincsSubmission.submission.runWith hash .expand (message, pk, signature)
  simp only [h] at value finished cycles calls blocks
  cases value
  cases finished
  cases cycles
  cases calls
  cases blocks
  rfl

/-- info: 'SigGolfCandidate.Sphincs.expand_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms expand_exact

end SigGolfCandidate.Sphincs
