import SigGolfCandidate.SphincsExpansion
import SigGolfCandidate.Memory
import RiscvZkvm.Rv64.Logic.MemRegion

namespace SigGolfCandidate.Sphincs.Expansion
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64

private def source (i : Nat) : Word := BitVec.ofNat 64 (0x20060 + 8 * i)
private def destination (i : Nat) : Word := BitVec.ofNat 64 (0x22ca0 + 8 * i)

private theorem source_value (i : Nat) (hi : i ≤ 1415) :
    (source i).toNat = 0x20060 + 8 * i := by
  have bound : 0x20060 + 8 * i < 2 ^ 64 := by omega
  exact Nat.mod_eq_of_lt bound

private theorem destination_value (i : Nat) (hi : i < 1415) :
    (destination i).toNat = 0x22ca0 + 8 * i := by
  have bound : 0x22ca0 + 8 * i < 2 ^ 64 := by omega
  exact Nat.mod_eq_of_lt bound

private theorem disjoint (i j : Nat) (hi : i ≤ 1415) (hj : j < 1415) :
    source i ≠ destination j := by
  intro h
  have eq := congrArg BitVec.toNat h
  rw [source_value i hi, destination_value j hj] at eq
  omega

private theorem destination_injective (i j : Nat) (hi : i < 1415) (hj : j < 1415)
    (ne : i ≠ j) : destination i ≠ destination j := by
  intro h
  have eq := congrArg BitVec.toNat h
  rw [destination_value i hi, destination_value j hj] at eq
  omega

/-- Source words remain intact and the completed destination prefix matches them. -/
private def Copied (original : MachineState) (n : Nat) (s : MachineState) : Prop :=
  (∀ i, i ≤ 1415 → s.getMem (source i) = original.getMem (source i)) ∧
  (∀ i, i < 1415 - n → s.getMem (destination i) = original.getMem (source i))

private theorem copy_next (original s : MachineState) (n : Nat)
    (inv : Invariant (n + 1) s) (copied : Copied original (n + 1) s) :
    Copied original n (loopNext s) := by
  obtain ⟨hn, _, src, dst, _⟩ := inv
  have hindex : 1415 - (n + 1) < 1415 := by omega
  change s.getReg .x6 = source (1415 - (n + 1)) at src
  change s.getReg .x7 = destination (1415 - (n + 1)) at dst
  constructor
  · intro i hi
    rw [loop_next_mem, dst, if_neg (disjoint i _ hi hindex)]
    exact copied.1 i hi
  · intro i hi
    have hib : i < 1415 := by omega
    by_cases heq : i = 1415 - (n + 1)
    · subst i
      rw [loop_next_mem, dst, src, if_pos rfl]
      exact copied.1 _ (by omega)
    · rw [loop_next_mem, dst, if_neg (destination_injective i _ hib hindex heq)]
      exact copied.2 i (by omega)



private theorem tail_mem_ne (s : MachineState) (a : Word)
    (h : a ≠ alignToDword (s.getReg .x7)) :
    (tailState s).getMem a = s.getMem a := by
  simp [tailState, execInstrBr, MachineState.setWord32, signExtend12,
    MachineState.getReg_setReg_ne, h]


private theorem tail_preserves (original s : MachineState)
    (inv : Invariant 0 s) (copied : Copied original 0 s) :
    Copied original 0 (tailState s) := by
  have dst : s.getReg .x7 = destination 1415 := by
    exact inv.2.2.2.1
  have tailAddr : alignToDword (s.getReg .x7) = destination 1415 := by
    rw [dst]
    decide
  have tailVal : (destination 1415).toNat = 0x258d8 := by decide
  constructor
  · intro i hi
    have ne : source i ≠ destination 1415 := by
      intro h
      have eq := congrArg BitVec.toNat h
      rw [source_value i hi, tailVal] at eq
      omega
    rw [tail_mem_ne s _ (by rw [tailAddr]; exact ne)]
    exact copied.1 i hi
  · intro i hi
    have ne : destination i ≠ destination 1415 := by
      intro h
      have eq := congrArg BitVec.toNat h
      rw [destination_value i hi, tailVal] at eq
      omega
    rw [tail_mem_ne s _ (by rw [tailAddr]; exact ne)]
    exact copied.2 i hi


private theorem finish_mem (s : MachineState) (a : Word) :
    (finishState s).getMem a = s.getMem a := by
  simp [finishState, execInstrBr]

private theorem prefix_mem (s : MachineState) (a : Word) :
    (prefixState s).getMem a = s.getMem a := by
  simp [prefixState, execInstrBr]

private theorem tail_word (s : MachineState)
    (src : s.getReg .x6 = source 1415)
    (dst : s.getReg .x7 = destination 1415) :
    (tailState s).getMem (destination 1415) =
      replaceWord32 (s.getMem (destination 1415)) 0
        ((s.getMem (source 1415)).truncate 32) := by
  simp [tailState, execInstrBr, MachineState.setWord32,
    MachineState.getWord32, signExtend12, src, dst, source, destination,
    MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq,
    alignToDword, byteOffset, extractWord32]


private theorem tail_bytes (s : MachineState)
    (src : s.getReg .x6 = source 1415)
    (dst : s.getReg .x7 = destination 1415)
    (i : Nat) (hi : i < 4) :
    (tailState s).getByte (BitVec.ofNat 64 (0x258d8 + i)) =
      s.getByte (BitVec.ofNat 64 (0x22c98 + i)) := by
  interval_cases i <;>
    change extractByte ((tailState s).getMem (destination 1415)) _ =
      extractByte (s.getMem (source 1415)) _ <;>
    rw [tail_word s src dst] <;>
    simp [extractByte, replaceWord32, byteOffset] <;>
    apply BitVec.eq_of_getLsbD_eq <;>
    intro j hj <;>
    interval_cases j <;> simp_all

private theorem source_tail_byte (original s : MachineState)
    (same : s.getMem (source 1415) = original.getMem (source 1415))
    (i : Nat) (hi : i < 4) :
    s.getByte (BitVec.ofNat 64 (0x22c98 + i)) =
      original.getByte (BitVec.ofNat 64 (0x22c98 + i)) := by
  interval_cases i <;>
    change extractByte (s.getMem (source 1415)) _ =
      extractByte (original.getMem (source 1415)) _ <;>
    rw [same]

private theorem loop_copies (hash : Hash) (original : MachineState)
    (n : Nat) (s : MachineState)
    (inv : Invariant n s) (copied : Copied original n s) :
    ∃ final, Executes hash expand s (6 * n + 5)
      ⟨.success, final, 6 * n + 5, 0, 0⟩ ∧
      (∀ i, i < 1415 → final.getMem (destination i) = original.getMem (source i)) ∧
      (∀ i, i < 4 → final.getByte (BitVec.ofNat 64 (0x258d8 + i)) =
        original.getByte (BitVec.ofNat 64 (0x22c98 + i))) := by
  induction n generalizing s with
  | zero =>
    refine ⟨finishState (tailState s), tail_executes hash s inv, ?_, ?_⟩
    · intro i hi
      rw [finish_mem]
      exact (tail_preserves original s inv copied).2 i hi
    · intro i hi
      simp only [MachineState.getByte, finish_mem]
      have hs : s.getReg .x6 = source 1415 := inv.2.2.1
      have hd : s.getReg .x7 = destination 1415 := inv.2.2.2.1
      exact (tail_bytes s hs hd i hi).trans
        (source_tail_byte original s (copied.1 1415 (by omega)) i hi)
  | succ n ih =>
    obtain ⟨final, trace, output, tailOutput⟩ := ih (loopNext s)
      (loop_invariant n s inv) (copy_next original s n inv copied)
    refine ⟨final, ?_, output, tailOutput⟩
    have block := loop_block s (by simpa using inv.2.1)
      (loop_accesses n s inv).1 (loop_accesses n s inv).2
    have hsteps : 6 * n + 5 + 6 = 6 * (n + 1) + 5 := by omega
    have hcycles : 6 + (6 * n + 5) = 6 * (n + 1) + 5 := by omega
    simpa only [Execution.charge, hsteps, hcycles, Nat.zero_add] using
      block.then_executes trace

/-- All complete doublewords are copied exactly by the submitted image. -/
theorem copies_words (hash : Hash) (s : MachineState) (pc : s.pc = 0x1000) :
    ∃ final, Executes hash expand s 8500 ⟨.success, final, 8500, 0, 0⟩ ∧
      ∀ i, i < 1415 →
        final.getMem (BitVec.ofNat 64 (0x22ca0 + 8 * i)) =
          s.getMem (BitVec.ofNat 64 (0x20060 + 8 * i)) := by
  have initial : Copied s 1415 (prefixState s) := by
    constructor
    · intro i _
      exact prefix_mem s _
    · intro i hi
      omega
  obtain ⟨final, trace, output, _⟩ := loop_copies hash s 1415 (prefixState s)
    (prefix_invariant s pc) initial
  refine ⟨final, ?_, output⟩
  have hsteps : (6 * 1415 + 5) + 5 = 8500 := by decide
  have hcycles : 5 + (6 * 1415 + 5) = 8500 := by decide
  simpa only [Execution.charge, hsteps, hcycles, Nat.zero_add] using
    (prefix_block s pc).then_executes trace

private theorem copied_bytes (original final : MachineState)
    (words : ∀ i, i < 1415 → final.getMem (destination i) = original.getMem (source i))
    (i : Nat) (hi : i < 11320) :
    final.getByte (BitVec.ofNat 64 (0x22ca0 + i)) = original.getByte (BitVec.ofNat 64 (0x20060 + i)) := by
  have dstAlign : (BitVec.ofNat 64 0x22ca0).toNat % 8 = 0 := by decide
  have srcAlign : (BitVec.ofNat 64 0x20060).toNat % 8 = 0 := by decide
  have dstBound : (BitVec.ofNat 64 0x22ca0).toNat + i < 2 ^ 64 := by change 142496 + i < 2 ^ 64; omega
  have srcBound : (BitVec.ofNat 64 0x20060).toNat + i < 2 ^ 64 := by change 131168 + i < 2 ^ 64; omega
  simp only [MachineState.getByte, BitVec.ofNat_add,
    alignToDword_add_ofNat_of_aligned dstAlign dstBound,
    alignToDword_add_ofNat_of_aligned srcAlign srcBound,
    byteOffset_add_ofNat_of_aligned dstAlign dstBound,
    byteOffset_add_ofNat_of_aligned srcAlign srcBound]
  apply congrArg (fun word => extractByte word (i % 8))
  simpa only [destination, source, BitVec.ofNat_add] using words (i / 8) (by omega)

/-- Every output byte, including the final four-byte word, matches its input byte. -/
theorem copies_bytes (hash : Hash) (s : MachineState) (pc : s.pc = 0x1000) :
    ∃ final, Executes hash expand s 8500 ⟨.success, final, 8500, 0, 0⟩ ∧
      ∀ i, i < 11324 →
        final.getByte (BitVec.ofNat 64 (0x22ca0 + i)) =
          s.getByte (BitVec.ofNat 64 (0x20060 + i)) := by
  have initial : Copied s 1415 (prefixState s) := by
    constructor
    · intro i _
      exact prefix_mem s _
    · intro i hi
      omega
  obtain ⟨final, trace, words, tail⟩ := loop_copies hash s 1415 (prefixState s)
    (prefix_invariant s pc) initial
  refine ⟨final, ?_, ?_⟩
  · have hsteps : (6 * 1415 + 5) + 5 = 8500 := by decide
    have hcycles : 5 + (6 * 1415 + 5) = 8500 := by decide
    simpa only [Execution.charge, hsteps, hcycles, Nat.zero_add] using
      (prefix_block s pc).then_executes trace
  · intro i hi
    by_cases hfull : i < 11320
    · exact copied_bytes s final words i hfull
    · have hj : i - 11320 < 4 := by omega
      have hd : 0x22ca0 + i = 0x258d8 + (i - 11320) := by omega
      have hs : 0x20060 + i = 0x22c98 + (i - 11320) := by omega
      rw [hd, hs]
      exact tail (i - 11320) hj

private theorem foldl_eq_on {α β : Type} (xs : List α) (f g : β → α → β)
    (same : ∀ x, x ∈ xs → ∀ acc, f acc x = g acc x) (acc : β) :
    xs.foldl f acc = xs.foldl g acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [same x (by simp)]
    exact ih (fun y hy => same y (by simp [hy])) _

/-- The source and destination have the same bytes under the organizer's output decoder. -/
theorem copies_buffer (hash : Hash) (s : MachineState) (pc : s.pc = 0x1000) :
    ∃ final, Executes hash expand s 8500 ⟨.success, final, 8500, 0, 0⟩ ∧
      readBuffer final 0x22ca0 SphincsWire.signatureBytes = readBuffer s 0x20060 SphincsWire.signatureBytes := by
  obtain ⟨final, trace, words⟩ := copies_bytes hash s pc
  refine ⟨final, trace, ?_⟩
  unfold readBuffer
  apply congrArg (BitVec.ofNat (8 * SphincsWire.signatureBytes))
  apply foldl_eq_on
  intro i hi acc
  rw [words i (by simpa [SphincsWire.signatureBytes_eq] using hi)]

/-- Expansion preserves the signature buffer through the official submission interface. -/
theorem run_copies_buffer (hash : Hash) (input : Input SphincsSubmission.submission.sizes .expand) :
    ∃ initial, initialState SphincsSubmission.submission .expand input = some initial ∧
      (SphincsSubmission.submission.runWith hash .expand input).value = some (readBuffer initial 0x20060 SphincsWire.signatureBytes) := by
  obtain ⟨initial, loaded, pc⟩ := initialState_exists SphincsSubmission.submission SphincsSubmission.admissible .expand input
  obtain ⟨final, trace, same⟩ := copies_buffer hash initial pc
  have run := runWith_of_executes SphincsSubmission.submission hash .expand input initial 8500
    ⟨.success, final, 8500, 0, 0⟩ loaded trace (by decide)
  refine ⟨initial, loaded, ?_⟩
  rw [run]
  change some (readBuffer final (witnessBase SphincsSubmission.submission.sizes) SphincsWire.signatureBytes) = _
  rw [show witnessBase SphincsSubmission.submission.sizes = 0x22ca0 from by decide]
  exact congrArg some same

set_option maxRecDepth 4096 in
/-- Expansion returns the exact typed signature through the official loader and decoder. -/
theorem run_identity (hash : Hash) (input : Input SphincsSubmission.submission.sizes .expand) :
    (SphincsSubmission.submission.runWith hash .expand input).value = some input.2.2 := by
  rcases input with ⟨message, pk, signature⟩
  obtain ⟨initial, loaded, output⟩ := run_copies_buffer hash (message, pk, signature)
  rw [output]
  apply congrArg some
  unfold initialState at loaded
  rw [if_pos (SphincsSubmission.admissible.2 .expand)] at loaded
  cases Option.some.inj loaded
  dsimp only [inputBuffers, Riscv.standardLayout, Layout.message, Layout.secretKey, Layout.publicKey, Layout.cache, Layout.signature, Layout.witness, List.foldl_cons, List.foldl_nil]
  rw [Memory.readBuffer_setReg]
  exact Memory.read_write_buffer _ 0x20060 SphincsWire.signatureBytes signature (by decide) (by decide)

/-- info: 'SigGolfCandidate.Sphincs.Expansion.run_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_identity

/-- info: 'SigGolfCandidate.Sphincs.Expansion.copies_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms copies_bytes

end SigGolfCandidate.Sphincs.Expansion
