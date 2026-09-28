import SigGolf

namespace SigGolf.Tests
open OracleComp OracleSpec Riscv RiscvZkvm.Rv64

private def zeroHash : Hash := fun _ => 0
private def addi (rd rs : Nat) (immediate : Nat) : BitVec 32 :=
  BitVec.ofNat 32 ((immediate % 4096) * 2 ^ 20 + rs * 2 ^ 15 + rd * 2 ^ 7 + 0x13)
private def acceptImage : Image := ⟨[addi 5 0 1, 0x73], []⟩
private def hashImage (bytes : Nat) : Image :=
  ⟨[addi 10 0 0, addi 11 0 bytes, addi 12 0 0, 0x73, addi 5 0 1, addi 10 0 0, 0x73], []⟩

/-- A layout with the cache at `0x60` and the signature and witness following it. -/
private def signatureBase (sizes : Sizes) : Nat := 0x60 + 8 * ((sizes.cache + 7) / 8)
private def witnessBase (sizes : Sizes) : Nat := signatureBase sizes + 8 * ((sizes.signature + 7) / 8)
private def standardLayout (sizes : Sizes) : Layout :=
  { message := 0, secretKey := 0x20, publicKey := 0x40, cache := 0x60,
    signature := signatureBase sizes, witness := witnessBase sizes }

private def toySizes : Sizes := ⟨1, 1, 2 ^ 17⟩
private def toy : Submission := ⟨toySizes, standardLayout toySizes, fun _ => hashImage 128⟩
private def movedLayout : Layout :=
  { message := 0x40000, secretKey := 0x40020, publicKey := 0x40040, cache := 0x50000,
    signature := 0x80000, witness := 0x81000 }
private def movedToy : Submission := { toy with layout := movedLayout }
private def runSmall (image : Image) (state : MachineState := initialMachine) : Execution :=
  evalWithAnswerFn zeroHash (execute image 20 state)

-- Kernel-checked boundary cases, independent of the compiled evaluator.
example : Query.blocks ⟨0, 0⟩ = 1 ∧ Query.blocks ⟨1, 0⟩ = 2 := by decide
example : witnessCharge 0 = 0 ∧ witnessCharge 1 = 1 ∧ witnessCharge 256 = 1 ∧ witnessCharge 257 = 2 := by
  decide
example : accessValid 0 8 = true ∧ accessValid 1 8 = false := by decide
example : rangeValid 0xfffff8 8 = true ∧ rangeValid 0xfffff8 9 = false := by decide
example : rangeValid 0xffffffffffffffff 2 = false := by decide
example : accessValid 0x100000 8 = true ∧ accessValid 0x1000000 8 = false := by decide
example : MEMORY_BYTES = 16777216 ∧ MAX_PROGRAM_BYTES = 1048576 := by decide
example : Sizes.Valid ⟨2 ^ 14, 1, 0⟩ ∧ ¬ Sizes.Valid ⟨2 ^ 14 + 1, 1, 0⟩ ∧
    Sizes.Valid ⟨1, 1, 2 ^ 17⟩ ∧ ¬ Sizes.Valid ⟨1, 1, 2 ^ 17 + 1⟩ ∧ Sizes.Valid ⟨0, 0, 0⟩ := by decide
example : signatureBase ⟨1, 1, 0⟩ = 0x60 ∧ signatureBase ⟨1, 1, 9⟩ = 0x70 := by decide
example (image : Image) (sizes : Sizes) (h : image.byteSize = MAX_PROGRAM_BYTES) :
    ¬ image.Valid sizes (standardLayout sizes) := fun valid => by have := valid.1; omega
example : wordResult .div 0x80000000 0xffffffff = 0x80000000 := by decide
example : wordResult .div 7 0 = 0xffffffff ∧ wordResult .rem 7 0 = 7 := by decide
example : wordResult .sll 1 32 = 1 ∧ wordResult .sra 0x80000000 31 = 0xffffffff := by decide
example : witnessBase toySizes = 0x20068 ∧ witnessBase ⟨9, 1, 2 ^ 17⟩ = 0x20070 := by decide
example : (hashImage 128).Valid toySizes movedLayout := by decide
example : ¬ (hashImage 128).Valid toySizes { movedLayout with publicKey := movedLayout.message } := by
  decide
example : ¬ ({ hashImage 128 with data := List.replicate 32 0 } : Image).Valid toySizes
    { standardLayout toySizes with witness := MEMORY_BYTES - 16 } := by decide
example : toy.Admission := by decide

/-- A run cut off after `steps` instructions has spent at least `steps` cycles, so `Termination`
needs only the cycle bound. -/
theorem unfinished_cycles (hash : Hash) (image : Image) :
    ∀ (steps : Nat) (state : MachineState),
      (evalWithAnswerFn hash (execute image steps state)).exit = .unfinished →
        steps ≤ (evalWithAnswerFn hash (execute image steps state)).cycles := by
  intro steps
  induction steps with
  | zero => intro state _; exact Nat.zero_le _
  | succ steps ih =>
    intro state
    simp only [execute]
    split
    · simp
    · split
      · simp only [bind_pure_comp, evalWithAnswerFn_bind, evalWithAnswerFn_map, Execution.charge]
        intro h
        have := ih _ h
        have hb : 1 ≤ (hashInput state).blocks := Nat.le_add_left 1 _
        omega
      · split
        · intro h; split at h <;> simp at h
        · simp
    · split
      · simp
      · simp only [bind_pure_comp, evalWithAnswerFn_map, Execution.charge]
        intro h
        have := ih _ h
        have hc : 1 ≤ instructionCycles ‹Instruction› := by unfold instructionCycles; split <;> omega
        omega

/-- Coins answer zero and every hash answers zero. -/
private def fixedWorld : QueryImpl World Id
  | .inl n => (0 : Fin (n + 1))
  | .inr _ => (0 : BitVec 256)

/-- The fixed world with the experiment's own hash-call charging. -/
private def fixedCounted := fixedWorld.withAddCost hashCost

private def hashQuery (input : Query) : OracleComp (World + SigningSpec toy.sizes) (BitVec 256) :=
  liftM (OracleSpec.query (spec := World + SigningSpec toy.sizes) (.inl (.inr input)))
private def signQuery (request : SigningRequest toy.sizes) :
    OracleComp (World + SigningSpec toy.sizes) (Option (Bytes toy.sizes.signature)) :=
  liftM (OracleSpec.query (spec := World + SigningSpec toy.sizes) (.inr request))

/-- Two hash queries, then a witness for message 8. -/
private def repeatHasher : Adversary toy.sizes := fun _ _ => do
  let _ ← hashQuery ⟨0, 0⟩
  let _ ← hashQuery ⟨0, 0⟩
  return some (.witness 8 0)

/-- One signing request, then the given forgery. -/
private def signer (request : SigningRequest toy.sizes) (final : Option (Forgery toy.sizes)) :
    Adversary toy.sizes := fun _ _ => do
  let _ ← signQuery request
  return final

/-- Gives up without submitting. -/
private def quitter : Adversary toy.sizes := fun _ _ => return none

private def cacheEcho : Submission where
  sizes := toySizes
  layout := standardLayout toySizes
  image
    | .sign => ⟨(hashImage 128).code.take 4 ++
        [0x00020437, addi 8 8 0x60, 0x06004383, 0x00740023, addi 5 0 1, addi 10 0 0, 0x73], []⟩
    | _ => acceptImage

private def failedSign : Submission where
  sizes := toySizes
  layout := standardLayout toySizes
  image
    | .sign => ⟨(hashImage 128).code.take 4 ++ [addi 5 0 1, addi 10 0 1, 0x73], []⟩
    | program => cacheEcho.image program

/-- Run an adversary against a submission's signing oracle in the fixed world, counting hash calls. -/
private def interact (submission : Submission) (adversary : Adversary submission.sizes) :
    (Option (Forgery submission.sizes) × SigningLog submission.sizes) × Nat :=
  Id.run (simulateQ fixedCounted (submission.interact 0 adversary 0 0)).run

/-- Judge a forgery in the fixed world, counting hash calls. -/
private def judge (submission : Submission) (log : SigningLog submission.sizes)
    (forgery : Forgery submission.sizes) : Bool × Nat :=
  Id.run (simulateQ fixedCounted
    (liftM (submission.checkForgery 0 log forgery) : OracleComp World Bool)).run

private def check (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError label)

-- Interpreter and game regressions, not a certificate for the deliberately insecure toy programs.
#eval do
  let halted := runSmall acceptImage
  check "HALT is charged" (halted.exit == Exit.success && halted.cycles == 2)
  let one := runSmall (hashImage 64)
  let two := runSmall (hashImage 128)
  check "HASH has no extra ECALL charge" (one.cycles == 14 && two.cycles == 22)
  check "HASH is charged per block" (one.compressions == 1 && two.compressions == 2)
  let partialBlock := runSmall (hashImage 72)
  check "HASH rejects partial blocks" (partialBlock.exit == Exit.failure && partialBlock.compressions == 0)
  check "multiplication and division cost four cycles"
    ((runSmall ⟨[0x020000b3, 0x020040b3, 0x020070bb, 0x000000b3, addi 5 0 1, 0x73], []⟩).cycles == 15)
  let emptyHash := runSmall (hashImage 0)
  check "HASH rejects empty input" (emptyHash.exit == Exit.failure && emptyHash.compressions == 0)
  let looping := runSmall ⟨[0x0000006f], []⟩
  check "cut-off runs report unfinished" (looping.exit == Exit.unfinished && looping.cycles == 20)
  check "malformed ECALL encoding fails" (decodeInstruction 0x000000f3 |>.isNone)
  check "CSR instructions are not exposed" (decodeInstruction 0x00002073 |>.isNone)
  check "EBREAK fails" ((runSmall ⟨[0x00100073], []⟩).exit == Exit.failure)
  check "nonzero exit code fails" ((runSmall ⟨[addi 5 0 1, addi 10 0 2, 0x73], []⟩).exit == Exit.failure)
  check "unknown services fail" ((runSmall ⟨[addi 5 0 7, 0x73], []⟩).exit == Exit.failure)
  check "misaligned PC fails" ((runSmall acceptImage { initialMachine with pc := 0x1002 }).exit == Exit.failure)
  check "x0 stays zero" ((initialMachine.setReg .x0 123).getReg .x0 == 0)
  check "all RV64 word operations decode"
    ([0x007302bb, 0x407302bb, 0x007312bb, 0x007352bb, 0x407352bb,
      0x027302bb, 0x027342bb, 0x027352bb, 0x027362bb, 0x027372bb,
      0x0013129b, 0x0013529b, 0x4013529b].all (fun w => (decodeInstruction w).isSome))
  let state := ((initialMachine.setReg .x10 0).setReg .x11 64).setReg .x12 0
  let state := (state.setByte 0 0xa5).setByte 1 0xff
  check "HASH accepts one aligned block" (hashArgumentsValid state)
  check "HASH reads little-endian bytes" ((hashInput state).blocks == 1 && (hashInput state).2.toNat == 0xffa5)
  let written := writeHash state 0x1234
  check "HASH writes little-endian and preserves registers"
    (written.getByte 0 == 0x34 && written.getByte 1 == 0x12 && written.getReg .x11 == 64 && written.pc == 0x1004)
  check "HASH rejects unaligned input" (!hashArgumentsValid (state.setReg .x10 1))
  check "HASH rejects unaligned output" (!hashArgumentsValid (state.setReg .x12 4))
  check "HASH rejects output crossing memory end" (!hashArgumentsValid (state.setReg .x12 0xfffff8))
  check "HASH rejects lengths that are not whole blocks" (!hashArgumentsValid (state.setReg .x11 72))
  check "HASH accepts a final in-bounds block" (hashArgumentsValid (state.setReg .x10 0xffffc0))
  check "HASH rejects input crossing memory end" (!hashArgumentsValid (state.setReg .x10 0xffffc8))
  let faulty := runSmall ⟨[0x73], []⟩ (state.setReg .x12 0xfffff8)
  check "invalid HASH makes no oracle call" (faulty.exit == Exit.failure && faulty.compressions == 0)
  check "load at address zero is valid" (memoryArgumentsValid initialMachine (.LD .x1 .x0 0))
  check "load alignment is enforced" (!memoryArgumentsValid initialMachine (.LD .x1 .x0 1))
  -- The signing log and its freshness predicates.
  let log : SigningLog toy.sizes := [⟨⟨7, 0⟩, some 9⟩, ⟨⟨5, 0⟩, none⟩]
  check "a log within the lifetime is valid" (decide log.WithinLifetime)
  check "witness replays excluded by message" (decide (log.Signed 7) && !decide (log.Signed 8))
  check "failed signing adds no replay entry" (!decide (log.Signed 5))
  check "signature replays excluded by exact pair"
    (decide (log.Contains 7 9) && !decide (log.Contains 7 10))
  -- The final check, counting its own hash calls.
  check "witness final check charged" (judge toy log (.witness 8 0) == (true, 1))
  check "expansion and final verification charged" (judge toy log (.signature 7 10) == (true, 2))
  check "signature replay loses despite acceptance" (judge toy log (.signature 7 9) == (false, 2))
  check "signed-message witness loses despite acceptance" (judge toy log (.witness 7 0) == (false, 1))
  -- The adversary's oracles, counting its hash calls and logging its signing requests.
  let ((outcome, played), calls) := interact toy repeatHasher
  check "attacker hash queries are charged and nothing is logged"
    ((outcome matches some (.witness 8 _)) && calls == 2 && played.isEmpty)
  let ((quit, _), quitCalls) := interact toy quitter
  check "giving up submits nothing and costs nothing" (quit.isNone && quitCalls == 0)
  let ((_, signed), signCalls) := interact toy (signer ⟨7, 0⟩ (some (.witness 8 0)))
  let loggedSeven := match signed with | [entry] => entry.1.message == 7 && entry.2 == some 0 | _ => false
  check "signing is logged and its work is charged" (signCalls == 1 && loggedSeven)
  let ((_, echoed), _) := interact cacheEcho (signer ⟨7, 0xa5⟩ none)
  let echoedByte := match echoed with | [entry] => entry.2 == some (0xa5 : BitVec 8) | _ => false
  check "attacker cache reaches sign" echoedByte
  let ((_, denied), deniedCalls) := interact failedSign (signer ⟨7, 0⟩ none)
  let loggedFailure := match denied with | [entry] => entry.2.isNone | _ => false
  check "failed signing is logged as a failure and retains its cost" (deniedCalls == 1 && loggedFailure)
  -- Loading and outputs.
  let state := initialState toy .verify (0x34, 0x56, 0x78)
  check "fixed input buffers" (state.getByte 0 == 0x34 && state.getByte 0x40 == 0x56 &&
    state.getByte (BitVec.ofNat 64 (witnessBase toySizes)) == 0x78)
  check "undeclared secretKey and cache are zero" (state.getByte 0x20 == 0 && state.getByte 0x60 == 0)
  check "initial registers" (state.pc == 0x1000 && state.getReg .x2 == 0x1000000 && state.getReg .x10 == 0)
  let state := initialState toy .sign (0x12, 0x9a, 0x34)
  check "sign inputs exclude the public key" (state.getByte 0x20 == 0x12 &&
    state.getByte 0x60 == 0x9a && state.getByte 0 == 0x34 && state.getByte 0x40 == 0)
  let state := initialState movedToy .verify (0x34, 0x56, 0x78)
  check "custom input offsets" (state.getByte movedLayout.message == 0x34 &&
    state.getByte movedLayout.publicKey == 0x56 && state.getByte movedLayout.witness == 0x78)
  check "former input offsets stay zero" (state.getByte 0x40 == 0 &&
    state.getByte (BitVec.ofNat 64 (witnessBase toySizes)) == 0)
  let outputState := initialMachine.writeBytesAsWords (BitVec.ofNat 64 movedLayout.signature) [0x5a]
  let output : BitVec 8 := readOutput movedToy.sizes movedToy.layout .sign outputState
  check "custom output offset" (output == 0x5a)
  IO.println "RISC-V and security regressions passed."

/-- info: 'SigGolf.Certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SigGolf.Certificate

end SigGolf.Tests
