import SigGolf.Riscv

/-! # Programs

A submission's four programs and how each is loaded, run, and charged: inputs are written to
fresh zeroed memory, the image executes for at most `CYCLE_LIMIT` instructions, and the output
is read back. The honest experiment `keygen`, `sign`, `expand`, `verify` is defined here too,
once for one message and once over every message. -/

namespace SigGolf
open OracleComp RiscvZkvm.Rv64

/-- What a submission declares: the sizes `S`, `W`, `K`, one layout, and the image of each
program. -/
structure Submission where
  sizes : Sizes
  layout : Layout
  image : Program → Riscv.Image

/-! ### Loading -/

/-- Inputs loaded before each program runs. -/
def Input (sizes : Sizes) : Program → Type
  | .keygen => SecretKey
  | .sign => SecretKey × Bytes sizes.cache × Message
  | .expand => Message × PublicKey × Bytes sizes.signature
  | .verify => Message × PublicKey × Bytes sizes.witness

/-- Outputs read after a successful run; `verify` only accepts or rejects. -/
def Output (sizes : Sizes) : Program → Type
  | .keygen => PublicKey × Bytes sizes.cache
  | .sign => Bytes sizes.signature
  | .expand => Bytes sizes.witness
  | .verify => Unit

/-- Little-endian byte list of a fixed-size value, as `Riscv.readBuffer` reads it back. -/
def bytes {n : Nat} (value : Bytes n) : List Byte :=
  (List.range n).map fun i => value.extractLsb' (8 * i) 8

/-- Where each program's inputs are written. -/
def inputBuffers (sizes : Sizes) (layout : Layout) :
    (program : Program) → Input sizes program → List (Nat × List Byte)
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

/-- Fresh memory, the embedded data at `dataBase`, only the declared inputs, and `sp` at
`dataBase`. -/
def initialState (submission : Submission) (program : Program)
    (input : Input submission.sizes program) : MachineState :=
  let image := submission.image program
  let dataBase := BitVec.ofNat 64 (Riscv.dataBase image)
  let withData := Riscv.initialMachine.writeBytesAsWords dataBase image.data
  let loaded := (inputBuffers submission.sizes submission.layout program input).foldl
    (fun state buffer => state.writeBytesAsWords (BitVec.ofNat 64 buffer.1) buffer.2) withData
  loaded.setReg .x2 dataBase

/-- Where each program's output is read. -/
def readOutput (sizes : Sizes) (layout : Layout) :
    (program : Program) → MachineState → Output sizes program
  | .keygen, state =>
      (Riscv.readBuffer state layout.publicKey 16, Riscv.readBuffer state layout.cache sizes.cache)
  | .sign, state => Riscv.readBuffer state layout.signature sizes.signature
  | .expand, state => Riscv.readBuffer state layout.witness sizes.witness
  | .verify, _ => ()

/-! ### One run -/

/-- One execution: its output if it halted successfully, and its cycles and compressions. -/
structure RunResult (α : Type) where
  output : Option α
  cycles : Nat
  compressions : Nat

/-- Run one program on fresh memory for at most `CYCLE_LIMIT` instructions; a run cut off there
has no output. An image that fails `Image.Valid` is run as is; the statements below are meant
together with `Admission`. -/
def Submission.run (submission : Submission) (program : Program)
    (input : Input submission.sizes program) :
    OracleComp HashSpec (RunResult (Output submission.sizes program)) := do
  let execution ←
    Riscv.execute (submission.image program) CYCLE_LIMIT (initialState submission program input)
  let output := readOutput submission.sizes submission.layout program execution.state
  return ⟨if execution.exit = .success then some output else none,
    execution.cycles, execution.compressions⟩

/-! ### The honest experiment -/

/-- One honest experiment: whether it succeeded, each program's compressions, and the scored
verification cycles. -/
structure HonestResult where
  success : Bool
  compressions : Program → Nat
  verificationCycles : Nat

/-- The README's honest experiment, steps 1 to 4. Stop at the first failure; failed programs
remain charged and unreached ones cost zero. -/
def Submission.honest (submission : Submission) (secretKey : SecretKey) (message : Message) :
    OracleComp HashSpec HonestResult := do
  let mut compressions : Program → Nat := fun _ => 0
  -- 1. keygen
  let keygen ← submission.run .keygen secretKey
  compressions := Function.update compressions .keygen keygen.compressions
  let some (pk, cache) := keygen.output | return ⟨false, compressions, 0⟩
  -- 2. sign
  let sign ← submission.run .sign (secretKey, cache, message)
  compressions := Function.update compressions .sign sign.compressions
  let some signature := sign.output | return ⟨false, compressions, 0⟩
  -- 3. expand
  let expand ← submission.run .expand (message, pk, signature)
  compressions := Function.update compressions .expand expand.compressions
  let some witness := expand.output | return ⟨false, compressions, 0⟩
  -- 4. verify
  let verify ← submission.run .verify (message, pk, witness)
  compressions := Function.update compressions .verify verify.compressions
  return ⟨verify.output.isSome, compressions,
    verify.cycles + witnessCharge submission.sizes.witness⟩

/-- Runs the honest experiment for each of the 2^256 messages in turn against the same `H` and
reports whether all succeed. A mathematical definition, not something one can execute. -/
noncomputable def Submission.everyMessageSucceeds (submission : Submission)
    (secretKey : SecretKey) : OracleComp HashSpec Bool :=
  (·.all HonestResult.success) <$>
    (Finset.univ : Finset Message).toList.mapM (submission.honest secretKey)

end SigGolf
