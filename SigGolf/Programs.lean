import SigGolf.Riscv

/-! # Programs

A submission's four programs and how each is loaded, run, and charged: inputs are written to
fresh zeroed memory, the image executes for at most `CYCLE_LIMIT` instructions, and the output
is read back. The honest experiment `keygen`, `sign`, `expand`, `verify` is defined here too,
once for one message and once over every message. -/

namespace SigGolf
open OracleComp RiscvZkvm.Rv64

structure Submission where
  sizes : Sizes
  layout : Layout
  image : Program → Riscv.Image

/-! ### Loading -/

def Input (sizes : Sizes) : Program → Type
  | .keygen => SecretKey
  | .sign => SecretKey × Bytes sizes.cache × Message
  | .expand => Message × PublicKey × Bytes sizes.signature
  | .verify => Message × PublicKey × Bytes sizes.witness

/-- `verify` only accepts or rejects, so it has no output. -/
def Output (sizes : Sizes) : Program → Type
  | .keygen => PublicKey × Bytes sizes.cache
  | .sign => Bytes sizes.signature
  | .expand => Bytes sizes.witness
  | .verify => Unit

/-- Little-endian byte list of a fixed-size value, as `Riscv.readBuffer` reads it back. -/
def bytes {n : Nat} (value : Bytes n) : List Byte :=
  (List.range n).map fun i => value.extractLsb' (8 * i) 8

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

/-- Memory holds only the embedded data and the declared inputs; `sp`, register `x2`, starts at
`dataBase`. -/
def initialState (submission : Submission) (program : Program)
    (input : Input submission.sizes program) : MachineState :=
  let image := submission.image program
  let dataBase := BitVec.ofNat 64 (Riscv.dataBase image)
  let withData := Riscv.initialMachine.writeBytesAsWords dataBase image.data
  let loaded := (inputBuffers submission.sizes submission.layout program input).foldl
    (fun state (offset, data) => state.writeBytesAsWords (BitVec.ofNat 64 offset) data) withData
  loaded.setReg .x2 dataBase

def readOutput (sizes : Sizes) (layout : Layout) :
    (program : Program) → MachineState → Output sizes program
  | .keygen, state =>
      (Riscv.readBuffer state layout.publicKey 16, Riscv.readBuffer state layout.cache sizes.cache)
  | .sign, state => Riscv.readBuffer state layout.signature sizes.signature
  | .expand, state => Riscv.readBuffer state layout.witness sizes.witness
  | .verify, _ => ()

/-! ### One run -/

structure RunResult (α : Type) where
  output : Option α
  cycles : Nat
  compressions : Nat

/-- An image that fails `Image.Valid` is run as is; the statements are meant together with
`Admission`. -/
def Submission.run (submission : Submission) (program : Program)
    (input : Input submission.sizes program) :
    OracleComp HashSpec (RunResult (Output submission.sizes program)) := do
  let execution ←
    Riscv.execute (submission.image program) CYCLE_LIMIT (initialState submission program input)
  let output := readOutput submission.sizes submission.layout program execution.state
  return ⟨if execution.exit = .success then some output else none,
    execution.cycles, execution.compressions⟩

/-! ### The honest experiment -/

structure HonestResult where
  success : Bool
  compressions : Program → Nat
  verificationCycles : Nat

/-- The README's honest experiment, steps 1 to 4. A failed program remains charged; unreached
ones cost zero. -/
def Submission.honest (submission : Submission) (secretKey : SecretKey) (message : Message) :
    OracleComp HashSpec HonestResult := do
  let mut charges : Program → Nat := fun _ => 0
  -- 1. keygen
  let keygen ← submission.run .keygen secretKey
  charges := Function.update charges .keygen keygen.compressions
  let some (pk, cache) := keygen.output
    | return { success := false, compressions := charges, verificationCycles := 0 }
  -- 2. sign
  let sign ← submission.run .sign (secretKey, cache, message)
  charges := Function.update charges .sign sign.compressions
  let some signature := sign.output
    | return { success := false, compressions := charges, verificationCycles := 0 }
  -- 3. expand
  let expand ← submission.run .expand (message, pk, signature)
  charges := Function.update charges .expand expand.compressions
  let some witness := expand.output
    | return { success := false, compressions := charges, verificationCycles := 0 }
  -- 4. verify
  let verify ← submission.run .verify (message, pk, witness)
  charges := Function.update charges .verify verify.compressions
  return { success := verify.output.isSome, compressions := charges,
           verificationCycles := verify.cycles + witnessCharge submission.sizes.witness }

/-- All 2^256 messages against the same `H`: a mathematical definition, not something one can
execute. -/
noncomputable def Submission.everyMessageSucceeds (submission : Submission)
    (secretKey : SecretKey) : OracleComp HashSpec Bool := do
  let mut allSucceeded := true
  for message in (Finset.univ : Finset Message).toList do
    let result ← submission.honest secretKey message
    allSucceeded := allSucceeded && result.success
  return allSucceeded

end SigGolf
