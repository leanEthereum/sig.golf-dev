import SigGolfCandidate.SphincsImages
import SigGolfCandidate.SphincsWire

namespace SigGolfCandidate.SphincsSubmission
open SigGolf

def sizes : Sizes := ⟨SphincsWire.signatureBytes, SphincsWire.signatureBytes⟩
def layout : Layout := Riscv.standardLayout sizes

def submission : Submission where
  sizes := sizes
  layout := layout
  image
    | .keygen => SphincsImages.keygen
    | .sign => SphincsImages.sign
    | .expand => SphincsImages.expand
    | .verify => SphincsImages.verify

/-- Candidate value. No organizer certificate is claimed in this module. -/
def cycleBound : Nat := 171399

theorem sizes_valid : sizes.Valid := by
  simp [Sizes.Valid, sizes, SphincsWire.signatureBytes_eq, MAX_WITNESS_BYTES]
theorem score_eq : submission.score cycleBound = 1940922276 := by decide

end SigGolfCandidate.SphincsSubmission
