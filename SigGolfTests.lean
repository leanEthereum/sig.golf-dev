import SigGolf

namespace SigGolf.Tests
open OracleComp OracleSpec Riscv RiscvZkvm.Rv64

private def blank : MachineState := { regs := fun _ => 0, mem := fun _ => 0, pc := 0x1000 }
private def zeroHash : Hash := fun _ => 0
private def addi (rd rs : Nat) (immediate : Nat) : BitVec 32 :=
  BitVec.ofNat 32 ((immediate % 4096) * 2 ^ 20 + rs * 2 ^ 15 + rd * 2 ^ 7 + 0x13)
private def acceptImage : Image := ⟨[addi 5 0 1, 0x73], []⟩
private def hashImage (bytes : Nat) : Image :=
  ⟨[addi 10 0 0, addi 11 0 bytes, addi 12 0 0, 0x73,
    addi 5 0 1, addi 10 0 0, 0x73], []⟩
private def toy : Submission := ⟨⟨1, 1, 2 ^ 17⟩, standardLayout ⟨1, 1, 2 ^ 17⟩, fun _ => hashImage 128⟩
private def movedLayout : Layout := ⟨0x40000, 0x40020, 0x40040, 0x50000, 0x80000, 0x81000⟩
private def movedToy : Submission := { toy with layout := movedLayout }
private def runSmall (image : Image) (state : MachineState := blank) : Execution :=
  evalWithAnswerFn zeroHash (execute 20 image state)

-- Kernel-checked boundary cases, independent of the compiled evaluator.
example : Query.blocks ⟨0, 0⟩ = 1 ∧ Query.blocks ⟨1, 0⟩ = 2 := by decide
example : witnessCycles 0 = 0 ∧ witnessCycles 1 = 1 ∧ witnessCycles 256 = 1 ∧ witnessCycles 257 = 2 := by decide
example : accessValid 0 8 = true ∧ accessValid 1 8 = false := by decide
example : rangeValid 0xfffff8 8 = true ∧ rangeValid 0xfffff8 9 = false := by decide
example : rangeValid 0xffffffffffffffff 2 = false := by decide
example : accessValid 0x100000 8 = true ∧ accessValid 0x1000000 8 = false := by decide
example : MEMORY_BYTES = 16777216 ∧ MAX_PROGRAM_BYTES = 1048576 := by decide
example : Sizes.Valid ⟨2 ^ 14, 1, 0⟩ ∧ ¬ Sizes.Valid ⟨2 ^ 14 + 1, 1, 0⟩ ∧
    Sizes.Valid ⟨1, 1, 2 ^ 17⟩ ∧ ¬ Sizes.Valid ⟨1, 1, 2 ^ 17 + 1⟩ ∧ Sizes.Valid ⟨0, 0, 0⟩ := by
  unfold Sizes.Valid MAX_SIGNATURE_BYTES MAX_WITNESS_BYTES MAX_CACHE_BYTES; decide
example : signatureBase ⟨1, 1, 0⟩ = 0x60 ∧ signatureBase ⟨1, 1, 9⟩ = 0x70 := by decide
example (image : Image) (sizes : Sizes) (h : image.byteSize = MAX_PROGRAM_BYTES) :
    ¬ image.Valid sizes (standardLayout sizes) := by
  intro valid
  have bound := valid.1
  omega
example : wordResult .div 0x80000000 0xffffffff = 0x80000000 := by decide
example : wordResult .div 7 0 = 0xffffffff ∧ wordResult .rem 7 0 = 7 := by decide
example : wordResult .sll 1 32 = 1 ∧ wordResult .sra 0x80000000 31 = 0xffffffff := by decide
example : witnessBase ⟨1, 1, 2 ^ 17⟩ = 0x20068 ∧ witnessBase ⟨9, 1, 2 ^ 17⟩ = 0x20070 := by decide
example : (hashImage 128).Valid ⟨1, 1, 2 ^ 17⟩ movedLayout := by decide
example : ¬ (hashImage 128).Valid ⟨1, 1, 2 ^ 17⟩
    { movedLayout with publicKey := movedLayout.message } := by decide
example : ¬ ({ hashImage 128 with data := List.replicate 32 0 } : Image).Valid ⟨1, 1, 2 ^ 17⟩
    { standardLayout ⟨1, 1, 2 ^ 17⟩ with witness := MEMORY_BYTES - 16 } := by decide

/-- Coins answer zero and every hash answers zero. -/
private def fixedWorld : QueryImpl World Id
  | .inl n => ⟨0, Nat.zero_lt_succ n⟩
  | .inr _ => (0 : BitVec 256)

/-- The fixed world with one unit charged per hash call, as the experiment charges. -/
private def fixedCounted := fixedWorld.withAddCost (fun | .inl _ => (0 : Nat) | .inr _ => 1)

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

/-- One signing request for message 7, then the given submission. -/
private def signer (final : Forgery toy.sizes) : Adversary toy.sizes := fun _ _ => do
  let _ ← signQuery ⟨7, 0⟩
  return some final

/-- Gives up without submitting. -/
private def quitter : Adversary toy.sizes := fun _ _ => return none

private def cacheEcho : Submission where
  sizes := ⟨1, 1, 2 ^ 17⟩
  layout := standardLayout ⟨1, 1, 2 ^ 17⟩
  image
    | .sign => ⟨(hashImage 128).code.take 4 ++
        [0x00020437, addi 8 8 0x60, 0x06004383, 0x00740023,
          addi 5 0 1, addi 10 0 0, 0x73], []⟩
    | _ => acceptImage

private def failedSign : Submission where
  sizes := ⟨1, 1, 2 ^ 17⟩
  layout := standardLayout ⟨1, 1, 2 ^ 17⟩
  image
    | .sign => ⟨(hashImage 128).code.take 4 ++ [addi 5 0 1, addi 10 0 1, 0x73], []⟩
    | phase => cacheEcho.image phase

/-- Run an adversary against a submission's signing oracle in the fixed world, counting hash calls. -/
private def interact (submission : Submission) (adversary : Adversary submission.sizes) :
    (Option (Forgery submission.sizes) × QueryLog (SigningSpec submission.sizes)) × Nat :=
  Id.run (simulateQ fixedCounted ((simulateQ
    (QueryImpl.ofLift World (WriterT (QueryLog (SigningSpec submission.sizes)) (OracleComp World)) +
      submission.signingOracle 0) (adversary 0 0)).run)).run

/-- Judge a submission in the fixed world, counting hash calls. -/
private def judge (submission : Submission) (log : QueryLog (SigningSpec submission.sizes))
    (forgery : Forgery submission.sizes) : Bool × Nat :=
  Id.run (simulateQ fixedCounted (liftM (submission.checkForgery 0 log forgery) : OracleComp World Bool)).run

private def check (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError label)

-- These are interpreter and game regressions, not a certificate for the deliberately insecure toy programs.
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
  check "observation exhaustion is not termination" (looping.exit == Exit.unfinished && looping.cycles == 20)
  check "malformed ECALL encoding fails" (decodeInstruction 0x000000f3 |>.isNone)
  check "CSR instructions are not exposed" (decodeInstruction 0x00002073 |>.isNone)
  check "EBREAK fails" ((runSmall ⟨[0x00100073], []⟩).exit == Exit.failure)
  check "nonzero exit code fails" ((runSmall ⟨[addi 5 0 1, addi 10 0 2, 0x73], []⟩).exit == Exit.failure)
  check "unknown services fail" ((runSmall ⟨[addi 5 0 7, 0x73], []⟩).exit == Exit.failure)
  check "misaligned PC fails" ((runSmall acceptImage { blank with pc := 0x1002 }).exit == Exit.failure)
  check "x0 stays zero" ((blank.setReg .x0 123).getReg .x0 == 0)
  check "all RV64 word operations decode"
    ([0x007302bb, 0x407302bb, 0x007312bb, 0x007352bb, 0x407352bb,
      0x027302bb, 0x027342bb, 0x027352bb, 0x027362bb, 0x027372bb,
      0x0013129b, 0x0013529b, 0x4013529b].all (fun w => (decodeInstruction w).isSome))
  let state := ((blank.setReg .x10 0).setReg .x11 64).setReg .x12 0
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
  check "HASH rejects input crossing memory end"
    (!hashArgumentsValid (state.setReg .x10 0xffffc8))
  let faulty := runSmall ⟨[0x73], []⟩ (state.setReg .x12 0xfffff8)
  check "invalid HASH makes no oracle call" (faulty.exit == Exit.failure && faulty.compressions == 0)
  check "load at address zero is valid" (memoryArgumentsValid blank (.LD .x1 .x0 0))
  check "load alignment is enforced" (!memoryArgumentsValid blank (.LD .x1 .x0 1))
  -- The signing log and its freshness predicates.
  let log : QueryLog (SigningSpec toy.sizes) := [⟨⟨7, 0⟩, some 9⟩, ⟨⟨5, 0⟩, none⟩]
  check "a log within the lifetime is valid" (decide (SigningLog.Valid log))
  check "witness replays excluded by message" (decide (SigningLog.Signed log 7) && !decide (SigningLog.Signed log 8))
  check "failed signing adds no replay entry" (!decide (SigningLog.Signed log 5))
  check "signature replays excluded by exact pair"
    (decide (SigningLog.Contains log 7 9) && !decide (SigningLog.Contains log 7 10))
  -- The final check, counting its own hash calls.
  check "witness final check charged" (judge toy log (.witness 8 0) == (true, 1))
  check "expansion and final verification charged" (judge toy log (.signature 7 10) == (true, 2))
  check "signature replay loses despite acceptance" (judge toy log (.signature 7 9) == (false, 2))
  check "signed-message witness loses despite acceptance" (judge toy log (.witness 7 0) == (false, 1))
  -- The adversary's oracles, counting its hash calls and logging its signing requests.
  let ((outcome, played), calls) := interact toy repeatHasher
  let submitted := match outcome with | some (.witness 8 _) => true | _ => false
  check "attacker hash queries are charged and nothing is logged" (submitted && calls == 2 && played.isEmpty)
  let ((quit, _), quitCalls) := interact toy quitter
  check "giving up submits nothing and costs nothing" (quit.isNone && quitCalls == 0)
  let ((_, signed), signCalls) := interact toy (signer (.witness 8 0))
  let loggedSeven := match signed with | [entry] => entry.1.message == 7 && entry.2 == some 0 | _ => false
  check "signing is logged and its work is charged" (signCalls == 1 && loggedSeven)
  let ((_, echoed), _) := interact cacheEcho (signer (.witness 8 0))
  let ((_, echoedCache), _) := interact cacheEcho (fun _ _ => do
    let _ ← liftM (OracleSpec.query (spec := World + SigningSpec cacheEcho.sizes) (.inr ⟨7, 0xa5⟩))
    return none)
  let echoedByte := match echoedCache with | [entry] => entry.2 == some (0xa5 : BitVec 8) | _ => false
  check "attacker cache reaches sign" (echoed.length == 1 && echoedByte)
  let ((_, denied), deniedCalls) := interact failedSign (signer (.witness 8 0))
  let loggedFailure := match denied with | [entry] => entry.2.isNone | _ => false
  check "failed signing is logged as a failure and retains its cost" (deniedCalls == 1 && loggedFailure)
  -- Loading and outputs.
  let initialized := initialState toy .verify (0x34, 0x56, 0x78)
  match initialized with
  | none => throw (IO.userError "admissible image rejected by loader")
  | some state =>
    check "fixed input buffers" (state.getByte 0 == 0x34 && state.getByte 0x40 == 0x56 &&
      state.getByte (BitVec.ofNat 64 (witnessBase toy.sizes)) == 0x78)
    check "undeclared secretKey and cache are zero" (state.getByte 0x20 == 0 && state.getByte 0x60 == 0)
    check "initial registers" (state.pc == 0x1000 && state.getReg .x2 == 0x1000000 && state.getReg .x10 == 0)
  match initialState toy .sign (0x12, 0x9a, 0x34) with
  | none => throw (IO.userError "admissible image rejected by loader")
  | some state =>
    check "sign inputs exclude the public key" (state.getByte 0x20 == 0x12 &&
      state.getByte 0x60 == 0x9a && state.getByte 0 == 0x34 && state.getByte 0x40 == 0)
  match initialState movedToy .verify (0x34, 0x56, 0x78) with
  | none => throw (IO.userError "custom layout rejected by loader")
  | some state =>
    check "custom input offsets" (state.getByte movedLayout.message == 0x34 &&
      state.getByte movedLayout.publicKey == 0x56 && state.getByte movedLayout.witness == 0x78)
    check "former input offsets stay zero" (state.getByte 0x40 == 0 &&
      state.getByte (BitVec.ofNat 64 (witnessBase movedToy.sizes)) == 0)
  let outputState := blank.writeBytesAsWords (BitVec.ofNat 64 movedLayout.signature) [0x5a]
  let output : BitVec 8 := readOutput movedToy.sizes movedToy.layout .sign outputState
  check "custom output offset" (output == 0x5a)
  IO.println "RISC-V and security regressions passed."

/-- info: 'SigGolf.Certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SigGolf.Certificate

end SigGolf.Tests
