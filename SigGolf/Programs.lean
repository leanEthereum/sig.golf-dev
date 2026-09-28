import SigGolf.Riscv

/-! # Programs

A submission's four programs and how each is loaded, run, and charged: inputs are written to
fresh zeroed memory, the image executes under `CYCLE_LIMIT`, and the output is read back. The
honest pipeline `keygen`, `sign`, `expand`, `verify` is defined here too, in the three forms the
statements need: under one fixed oracle, against a random oracle and message, and over every
message at once. -/

namespace SigGolf
open OracleComp OracleSpec RiscvZkvm.Rv64

/-- Every algorithm is fixed bytecode and embedded public data. -/
structure Submission where
  sizes : Sizes
  layout : Layout
  image : Phase → Riscv.Image

/-- Inputs loaded before each program runs. -/
def Input (sizes : Sizes) : Phase → Type
  | .keygen => SecretKey
  | .sign => SecretKey × Bytes sizes.cache × Message
  | .expand => Message × PublicKey × Bytes sizes.signature
  | .verify => Message × PublicKey × Bytes sizes.witness

/-- Outputs read after a successful run; `verify` only accepts or rejects. -/
def Output (sizes : Sizes) : Phase → Type
  | .keygen => PublicKey × Bytes sizes.cache
  | .sign => Bytes sizes.signature
  | .expand => Bytes sizes.witness
  | .verify => Unit

/-- Little-endian byte list of a fixed-size value. -/
def bytes {n : Nat} (value : Bytes n) : List Byte :=
  (List.range n).map fun i => value.extractLsb' (8 * i) 8

/-- The `n` bytes at `address`, read little-endian. -/
def readBuffer (state : MachineState) (address n : Nat) : Bytes n :=
  BitVec.ofNat (8 * n) ((List.range n).foldl
    (fun acc i => acc + (state.getByte (BitVec.ofNat 64 (address + i))).toNat * 2 ^ (8 * i)) 0)

/-- Where each program's inputs are written. -/
def inputBuffers (sizes : Sizes) (layout : Layout) :
    (phase : Phase) → Input sizes phase → List (Nat × List Byte)
  | .keygen, secretKey => [(layout.secretKey, bytes secretKey)]
  | .sign, (secretKey, cache, message) =>
      [(layout.secretKey, bytes secretKey), (layout.cache, bytes cache),
        (layout.message, bytes message)]
  | .expand, (message, pk, signature) =>
      [(layout.message, bytes message), (layout.publicKey, bytes pk),
        (layout.signature, bytes signature)]
  | .verify, (message, pk, witness) =>
      [(layout.message, bytes message), (layout.publicKey, bytes pk),
        (layout.witness, bytes witness)]

/-- Each execution starts with fresh zeroed memory and registers. Only declared inputs are loaded. -/
def initialState (submission : Submission) (phase : Phase) (input : Input submission.sizes phase) :
    Option MachineState :=
  let image := submission.image phase
  if image.Valid submission.sizes submission.layout then
    let blank : MachineState :=
      { regs := fun _ => 0, mem := fun _ => 0, pc := 0x1000 }
    let withData := blank.writeBytesAsWords (BitVec.ofNat 64 (Riscv.dataBase image)) image.data
    let loaded := (inputBuffers submission.sizes submission.layout phase input).foldl
      (fun state buffer => state.writeBytesAsWords (BitVec.ofNat 64 buffer.1) buffer.2) withData
    some (loaded.setReg .x2 (BitVec.ofNat 64 (Riscv.dataBase image)))
  else none

/-- Where each program's output is read. -/
def readOutput (sizes : Sizes) (layout : Layout) :
    (phase : Phase) → MachineState → Output sizes phase
  | .keygen, state =>
      (readBuffer state layout.publicKey 16, readBuffer state layout.cache sizes.cache)
  | .sign, state => readBuffer state layout.signature sizes.signature
  | .expand, state => readBuffer state layout.witness sizes.witness
  | .verify, _ => ()

/-- One execution: its output if it halted successfully, whether it halted within `CYCLE_LIMIT` instructions, and its cycles and compressions. -/
structure RunResult (α : Type) where
  value : Option α
  finished : Bool
  cycles : Nat
  compressions : Nat

/-- Run one program on fresh memory, observing at most `CYCLE_LIMIT` instructions. A run cut off there reports `finished = false` and never counts as terminating. -/
def Submission.run (submission : Submission) (phase : Phase) (input : Input submission.sizes phase) :
    OracleComp HashSpec (RunResult (Output submission.sizes phase)) := do
  match initialState submission phase input with
  | none => return ⟨none, true, 0, 0⟩ -- inadmissible image; excluded by `Admission`
  | some state =>
    let execution ← Riscv.execute CYCLE_LIMIT (submission.image phase) state
    return ⟨if execution.exit = .success then some (readOutput submission.sizes submission.layout phase execution.state)
      else none, execution.exit != .unfinished, execution.cycles, execution.compressions⟩

/-- Fixed-oracle meaning, used in termination and verification-cycle claims. -/
def Submission.runWith (submission : Submission) (hash : Hash) (phase : Phase)
    (input : Input submission.sizes phase) : RunResult (Output submission.sizes phase) :=
  evalWithAnswerFn hash (submission.run phase input)

/-- One honest pipeline: whether it succeeded, each phase's compressions, and the scored verification cycles. -/
structure HonestResult where
  success : Bool
  costs : Phase → Nat
  verificationCycles : Nat

/-- Set one phase's cost. -/
def recordCost (costs : Phase → Nat) (phase : Phase) (cost : Nat) : Phase → Nat :=
  fun other => if other = phase then cost else costs other

/-- One honest pipeline. Failed phases remain charged; phases not reached cost zero. -/
def Submission.honest (submission : Submission) (secretKey : SecretKey) (message : Message) :
    OracleComp HashSpec HonestResult := do
  let mut costs : Phase → Nat := fun _ => 0
  let keygen ← submission.run .keygen secretKey
  costs := recordCost costs .keygen keygen.compressions
  let some (pk, cache) := keygen.value | return ⟨false, costs, 0⟩
  let sign ← submission.run .sign (secretKey, cache, message)
  costs := recordCost costs .sign sign.compressions
  let some signature := sign.value | return ⟨false, costs, 0⟩
  let expand ← submission.run .expand (message, pk, signature)
  costs := recordCost costs .expand expand.compressions
  let some witness := expand.value | return ⟨false, costs, 0⟩
  let verify ← submission.run .verify (message, pk, witness)
  costs := recordCost costs .verify verify.compressions
  return ⟨verify.value.isSome, costs, verify.cycles + witnessCycles submission.sizes.witness⟩

/-- The honest pipeline under one fixed oracle, used in the verification-cycle claim. -/
def Submission.honestWith (submission : Submission) (hash : Hash) (secretKey : SecretKey)
    (message : Message) : HonestResult :=
  evalWithAnswerFn hash (submission.honest secretKey message)

/-- Benchmark one independent uniform message against one freshly sampled shared random oracle. -/
noncomputable def Submission.honestWorkload (submission : Submission) (secretKey : SecretKey) :
    ProbComp HonestResult := do
  let message ← ($ᵗ Message : ProbComp Message)
  withRandomOracle (submission.honest secretKey message)

/-- Whether every message succeeds against the same H. Under `withRandomOracle` this finite traversal defines a distribution; it is not an executable benchmark. -/
noncomputable def Submission.allSucceed (submission : Submission) (secretKey : SecretKey) :
    OracleComp HashSpec Bool :=
  (Finset.univ : Finset Message).toList.foldlM (fun ok message => do
    let result ← submission.honest secretKey message
    return ok && result.success) true

end SigGolf
