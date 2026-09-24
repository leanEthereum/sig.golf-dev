import SigGolfCandidate.SphincsVerifierLoader

/-!
# Public-key commitment check

The verifier compares the first two 64-bit words of its commitment HASH
answer with the 16-byte public key supplied by the organizer.
-/

namespace SigGolfCandidate.SphincsVerifierCommitmentCheck
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64

/-- Exact image words for the two commitment/public-key comparisons. -/
def comparePrefix : List (BitVec 32) := [
  0x00042337, 0x00030313, 0x04000393, 0x00033503,
  0x0003b583, 0x00b50463, 0xeb9ff06f, 0x00833503,
  0x0083b583, 0x00b50463, 0xea9ff06f]

theorem comparePrefix_eq :
    (SphincsImages.verify.code.drop 77).take 11 = comparePrefix := by
  decide

theorem fetch_compare (state : MachineState) (offset : Fin 11)
    (pc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * (77 + offset.val))) :
    fetch SphincsImages.verify state =
      (comparePrefix[offset.val]?).bind decodeInstruction := by
  have small : 0x1000 + 4 * (77 + offset.val) < 2 ^ 64 := by omega
  simp only [fetch, pc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
  have start : ¬ (0x1000 + 4 * (77 + offset.val) < 0x1000) := by omega
  have aligned : (0x1000 + 4 * (77 + offset.val)) % 4 = 0 := by omega
  simp only [start, decide_false, aligned, Bool.false_or]
  have index : (0x1000 + 4 * (77 + offset.val) - 0x1000) / 4 =
      77 + offset.val := by omega
  rw [index]
  rw [← List.getElem?_drop]
  rw [← List.getElem?_take_of_lt offset.isLt, comparePrefix_eq]
  simp

theorem writeHash_low (state : MachineState) (answer : BitVec 256)
    (destination : state.getReg .x12 = 0x42000) :
    (writeHash state answer).getMem 0x42000 =
      answer.extractLsb' 0 64 := by
  simp [writeHash, MachineState.writeWords_cons, destination]

theorem writeHash_high (state : MachineState) (answer : BitVec 256)
    (destination : state.getReg .x12 = 0x42000) :
    (writeHash state answer).getMem 0x42008 =
      answer.extractLsb' 64 64 := by
  simp [writeHash, MachineState.writeWords_cons, destination]

/-- info: 'SigGolfCandidate.SphincsVerifierCommitmentCheck.fetch_compare' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms fetch_compare

/-- info: 'SigGolfCandidate.SphincsVerifierCommitmentCheck.writeHash_low' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms writeHash_low

/-- info: 'SigGolfCandidate.SphincsVerifierCommitmentCheck.writeHash_high' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms writeHash_high

end SigGolfCandidate.SphincsVerifierCommitmentCheck
