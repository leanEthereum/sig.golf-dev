import SigGolf.Oracle
import RiscvZkvm.Rv64.Execution
import RiscvZkvm.Interpreter.Decode

/-! # RISC-V

The machine a submission's programs run on: a raw instruction image and its memory layout, the
RV64IM decoder, one execution step, the `HASH` and `HALT` system calls, and how cycles and
compressions are charged. The base RV64IM decoder and instruction semantics come from the pinned
`riscv-zkvm` model that ots.golf also uses; the W-suffixed word operations, the memory checks,
`HASH` and `HALT`, and all pricing are defined here. -/

namespace SigGolf.Riscv
open RiscvZkvm.Rv64 RiscvZkvm.Interpreter OracleComp OracleSpec

/-! ### Images and layout -/

/-- A program: 32-bit instruction encodings and the bytes loaded at `dataBase`. -/
structure Image where
  code : List (BitVec 32)
  data : List Byte
  deriving Repr

/-- The size bounded by `MAX_PROGRAM_BYTES`. -/
def Image.byteSize (image : Image) : Nat := 4 * image.code.length + image.data.length

/-- Embedded data sits at the top of memory, 16-byte aligned; `sp` starts here. -/
def dataBase (image : Image) : Nat := 16 * ((MEMORY_BYTES - image.data.length) / 16)
def signatureBase (sizes : Sizes) : Nat := 0x60 + 8 * ((sizes.cache + 7) / 8)
def witnessBase (sizes : Sizes) : Nat := signatureBase sizes + 8 * ((sizes.signature + 7) / 8)

/-- A reference layout: message, secret key, public key, then the cache, signature, and witness in sequence. Submissions may declare any valid layout. -/
def standardLayout (sizes : Sizes) : Layout :=
  ⟨0, 0x20, 0x40, 0x60, signatureBase sizes, witnessBase sizes⟩

def layoutBuffers (layout : Layout) (sizes : Sizes) : List (Nat × Nat) :=
  [(layout.message, 32), (layout.secretKey, 32), (layout.publicKey, 16),
   (layout.cache, sizes.cache), (layout.signature, sizes.signature),
   (layout.witness, sizes.witness)]

def disjointBuffers (left right : Nat × Nat) : Prop :=
  left.2 = 0 ∨ right.2 = 0 ∨ left.1 + left.2 ≤ right.1 ∨ right.1 + right.2 ≤ left.1

instance (left right : Nat × Nat) : Decidable (disjointBuffers left right) := by
  unfold disjointBuffers
  infer_instance

def buffersDisjoint : List (Nat × Nat) → Bool
  | [] => true
  | first :: rest =>
      rest.all (fun second => decide (disjointBuffers first second)) && buffersDisjoint rest

/-- Every buffer is 8-byte aligned and ends at or below the embedded data, and no two overlap. -/
def layoutValid (layout : Layout) (sizes : Sizes) (image : Image) : Prop :=
  (layoutBuffers layout sizes).all (fun buffer =>
    decide (buffer.1 % 8 = 0 ∧ buffer.1 + buffer.2 ≤ dataBase image)) = true ∧
  buffersDisjoint (layoutBuffers layout sizes) = true

instance (layout : Layout) (sizes : Sizes) (image : Image) :
    Decidable (layoutValid layout sizes image) := by
  unfold layoutValid
  infer_instance

/-- An image within the size bound whose layout fits below its data. -/
def Image.Valid (image : Image) (sizes : Sizes) (layout : Layout) : Prop :=
  image.byteSize < MAX_PROGRAM_BYTES ∧ layoutValid layout sizes image

instance (image : Image) (sizes : Sizes) (layout : Layout) : Decidable (image.Valid sizes layout) :=
  inferInstanceAs (Decidable (image.byteSize < MAX_PROGRAM_BYTES ∧ layoutValid layout sizes image))

/-- `bytes` bytes at `address` lie entirely in memory. -/
def rangeValid (address : BitVec 64) (bytes : Nat) : Bool :=
  decide (address.toNat + bytes ≤ MEMORY_BYTES)

/-- In memory and aligned to the access size. -/
def accessValid (address : BitVec 64) (bytes : Nat) : Bool :=
  rangeValid address bytes && decide (address.toNat % bytes = 0)

/-! ### Decoding -/

/-- Extensions needed to cover the complete RV64IM word-operation family. -/
inductive WordOp where
  | add | sub | sll | srl | sra | mul | div | divu | rem | remu
  deriving DecidableEq, Repr

/-- A decoded instruction: one from the upstream model, or a word operation it lacks. -/
inductive Instruction where
  | base (instruction : Instr)
  | word (op : WordOp) (rd rs1 rs2 : Reg)
  | sraiw (rd rs1 : Reg) (shift : BitVec 5)
  deriving Repr

/-- The program contains actual 32-bit encodings, never assembler pseudo-instructions. -/
def decodeInstruction (word : BitVec 32) : Option Instruction := do
  let opcode := (word.extractLsb' 0 7).toNat
  let rd := regOfBits (word.extractLsb' 7 5)
  let rs1 := regOfBits (word.extractLsb' 15 5)
  let rs2 := regOfBits (word.extractLsb' 20 5)
  let f3 := (word.extractLsb' 12 3).toNat
  let f7 := (word.extractLsb' 25 7).toNat
  if opcode = 0x73 then
    if word = 0x00000073 then return .base .ECALL
    else if word = 0x00100073 then return .base .EBREAK
    else none
  else if opcode = 0x3b then
    let op ← match f7, f3 with
      | 0, 0 => some WordOp.add
      | 0x20, 0 => some .sub
      | 0, 1 => some .sll
      | 0, 5 => some .srl
      | 0x20, 5 => some .sra
      | 1, 0 => some .mul
      | 1, 4 => some .div
      | 1, 5 => some .divu
      | 1, 6 => some .rem
      | 1, 7 => some .remu
      | _, _ => none
    return .word op rd rs1 rs2
  else if opcode = 0x1b && f3 = 5 && f7 = 0x20 then
    return .sraiw rd rs1 (word.extractLsb' 20 5)
  else
    return .base (← RiscvZkvm.Interpreter.decode word)

def wordResult (op : WordOp) (a b : BitVec 32) : BitVec 32 :=
  match op with
  | .add => a + b
  | .sub => a - b
  | .sll => a <<< (b.toNat % 32)
  | .srl => a >>> (b.toNat % 32)
  | .sra => a.sshiftRight (b.toNat % 32)
  | .mul => a * b
  | .div => if b = 0 then BitVec.allOnes 32 else a.sdiv b
  | .divu => if b = 0 then BitVec.allOnes 32 else a / b
  | .rem => if b = 0 then a else a.srem b
  | .remu => if b = 0 then a else a % b

/-! ### One step -/

/-- Every data access is bounds- and alignment-checked; address zero is an ordinary valid address. -/
def memoryArgumentsValid (state : MachineState) : Instr → Bool
  | .LB _ rs off | .LBU _ rs off | .SB rs _ off =>
      accessValid (state.getReg rs + signExtend12 off) 1
  | .LH _ rs off | .LHU _ rs off | .SH rs _ off =>
      accessValid (state.getReg rs + signExtend12 off) 2
  | .LW _ rs off | .LWU _ rs off | .SW rs _ off =>
      accessValid (state.getReg rs + signExtend12 off) 4
  | .LD _ rs off | .SD rs _ off =>
      accessValid (state.getReg rs + signExtend12 off) 8
  | _ => true

def ordinaryStep (state : MachineState) : Instruction → Option MachineState
  | .base (.ECALL) | .base (.EBREAK) | .base (.CSRS _ _) => none
  | .base (.LI _ _) | .base (.MV _ _) | .base (.NOP) => none
  | .base instruction =>
      if memoryArgumentsValid state instruction then some (execInstrBr state instruction) else none
  | .word op rd rs1 rs2 =>
      let value := wordResult op ((state.getReg rs1).truncate 32) ((state.getReg rs2).truncate 32)
      some ((state.setReg rd (value.signExtend 64)).setPC (state.pc + 4))
  | .sraiw rd rs shift =>
      let value := ((state.getReg rs).truncate 32).sshiftRight shift.toNat
      some ((state.setReg rd (value.signExtend 64)).setPC (state.pc + 4))

/-- Multiplication, division, and remainder instructions cost four cycles; every other ordinary instruction costs one. `ECALL` is priced in `execute`. -/
def instructionCycles : Instruction → Nat
  | .base (.MUL ..) | .base (.MULH ..) | .base (.MULHSU ..) | .base (.MULHU ..)
  | .base (.DIV ..) | .base (.DIVU ..) | .base (.REM ..) | .base (.REMU ..) => 4
  | .word .mul .. | .word .div .. | .word .divu .. | .word .rem .. | .word .remu .. => 4
  | _ => 1

/-- The instruction at `PC`: code starts at `0x1000`, four bytes per instruction. -/
def fetch (image : Image) (state : MachineState) : Option Instruction := do
  if state.pc.toNat < 0x1000 || state.pc.toNat % 4 != 0 then none else
    let word ← image.code[(state.pc.toNat - 0x1000) / 4]?
    decodeInstruction word

/-! ### HASH -/

/-- HASH reads whole 64-byte blocks: both addresses are 8-byte aligned, the byte length is a nonzero multiple of 64, and input and output lie in memory. -/
def hashArgumentsValid (state : MachineState) : Bool :=
  let source := state.getReg .x10
  let bytes := (state.getReg .x11).toNat
  let destination := state.getReg .x12
  decide (source.toNat % 8 = 0) && decide (0 < bytes ∧ bytes % 64 = 0) && rangeValid source bytes &&
    accessValid destination 8 && rangeValid destination 32

/-- The oracle input is the `a1` input bytes in increasing address order, `a1 / 64` blocks. -/
def hashInput (state : MachineState) : Query :=
  let n := (state.getReg .x11).toNat / 64 - 1
  ⟨n, BitVec.ofNat (8 * (64 * (n + 1))) ((List.range (64 * (n + 1))).foldl (fun acc i =>
    acc + (state.getByte (state.getReg .x10 + BitVec.ofNat 64 i)).toNat * 2 ^ (8 * i)) 0)⟩

/-- Write the 32-byte answer at `a2`, little-endian, and advance `PC`. -/
def writeHash (state : MachineState) (answer : BitVec 256) : MachineState :=
  (state.writeWords (state.getReg .x12)
    [answer.extractLsb' 0 64, answer.extractLsb' 64 64,
      answer.extractLsb' 128 64, answer.extractLsb' 192 64]).setPC (state.pc + 4)

/-! ### Execution and costs -/

/-- How a run ended: `HALT` with exit code 0, any fault or nonzero exit code, or cut off by the observation fuel. -/
inductive Exit where
  | success | failure | unfinished
  deriving DecidableEq, Repr

/-- A finished or cut-off run with its final state and charges. -/
structure Execution where
  exit : Exit
  state : MachineState
  cycles : Nat := 0
  hashCalls : Nat := 0
  hashCompressions : Nat := 0

/-- Add one instruction's cycles, hash calls, and compressions. -/
def Execution.charge (result : Execution) (cycles hashes blocks : Nat) : Execution :=
  { result with
    cycles := cycles + result.cycles
    hashCalls := hashes + result.hashCalls
    hashCompressions := blocks + result.hashCompressions }

/-- Fuel is a logical observation depth, not a VM timeout. Certification must exclude `unfinished` for every fixed oracle. -/
def execute : Nat → Image → MachineState → OracleComp HashSpec Execution
  | 0, _, state => pure ⟨.unfinished, state, 0, 0, 0⟩
  | fuel + 1, image, state =>
    match fetch image state with
    | none => pure ⟨.failure, state, 0, 0, 0⟩
    | some (.base .ECALL) =>
      if state.getReg .x5 = 0 && hashArgumentsValid state then do
        let input := hashInput state
        let answer ← HashSpec.query input
        let result ← execute fuel image (writeHash state answer)
        return result.charge (8 * input.blocks) 1 input.blocks
      else if state.getReg .x5 = 1 then
        pure ⟨if state.getReg .x10 = 0 then .success else .failure, state, 1, 0, 0⟩
      else pure ⟨.failure, state, 1, 0, 0⟩
    | some instruction =>
      match ordinaryStep state instruction with
      | none => pure ⟨.failure, state, 1, 0, 0⟩
      | some next => (fun result => result.charge (instructionCycles instruction) 0 0) <$>
          execute fuel image next

end SigGolf.Riscv
