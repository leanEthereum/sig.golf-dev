import SigGolfCandidate.SphincsImages
import SigGolfCandidate.SphincsWire

namespace SigGolfCandidate.SphincsExpandSmoke
open SigGolf OracleComp RiscvZkvm.Rv64
set_option maxRecDepth 16384

def submission : Submission where
  sizes := ⟨SphincsWire.signatureBytes, SphincsWire.signatureBytes⟩
  layout := Riscv.standardLayout ⟨SphincsWire.signatureBytes, SphincsWire.signatureBytes⟩
  image
    | .expand => SphincsImages.expand
    | _ => SphincsImages.verify

def smoke : Bool := Id.run do
  let signature : Bytes SphincsWire.signatureBytes := BitVec.ofNat _ 0x1234abcd
  let some state := initialState submission .expand (0, 0, signature) | return false
  let result := evalWithAnswerFn (fun _ => 0) (Riscv.execute 10000 SphincsImages.expand state)
  return result.exit == Riscv.Exit.success &&
    (result.state.getByte (BitVec.ofNat 64 (Riscv.witnessBase submission.sizes))).toNat == 0xcd &&
    (result.state.getByte (BitVec.ofNat 64 (Riscv.witnessBase submission.sizes + 1))).toNat == 0xab

#eval smoke

def verifyRejectsZero : Bool := Id.run do
  let witness : Bytes SphincsWire.signatureBytes := 0
  let some state := initialState submission .verify (0, 0, witness) | return false
  let result := evalWithAnswerFn (fun _ => 0) (Riscv.execute 100000 SphincsImages.verify state)
  return result.exit == Riscv.Exit.failure && result.hashCalls == 220

#eval verifyRejectsZero

end SigGolfCandidate.SphincsExpandSmoke
