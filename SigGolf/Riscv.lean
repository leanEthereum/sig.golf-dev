import SigGolf.Oracle
import RiscvZkvm.Rv64.Execution
import RiscvZkvm.Rv64.StepOn
import RiscvZkvm.Interpreter.Decode

/-! # RISC-V

The machine a submission's programs run on: a raw instruction image and its memory layout, the
RV64IM decoder, one execution step, the `HASH` and `HALT` system calls, and how cycles and
compressions are charged. The base RV64IM decoder and instruction semantics come from the pinned
`riscv-zkvm` model; the W-suffixed word operations, the memory checks, `HASH` and `HALT`, and all
pricing are defined here. -/

namespace SigGolf.Riscv
open RiscvZkvm.Rv64 RiscvZkvm.Interpreter OracleComp OracleSpec

/-! ### Images -/

/-- A program: 32-bit instruction encodings and the bytes loaded at `dataBase`. -/
structure Image where
  code : List (BitVec 32)
  data : List Byte

/-- `4 × instruction count + embedded-data bytes`, bounded by `MAX_PROGRAM_BYTES`. -/
def Image.byteSize (image : Image) : Nat := 4 * image.code.length + image.data.length

/-- Embedded data sits at the top of memory, 16-byte aligned; `sp` starts here. -/
def dataBase (image : Image) : Nat := 16 * ((MEMORY_BYTES - image.data.length) / 16)

/-! ### Layout -/

/-- Each object's buffer as `(address, length)`. -/
def layoutBuffers (layout : Layout) (sizes : Sizes) : List (Nat × Nat) :=
  [(layout.message, 32), (layout.secretKey, 32), (layout.publicKey, 16),
   (layout.cache, sizes.cache), (layout.signature, sizes.signature),
   (layout.witness, sizes.witness)]

/-- Two buffers do not overlap; an empty buffer overlaps nothing. -/
abbrev DisjointBuffers (left right : Nat × Nat) : Prop :=
  left.2 = 0 ∨ right.2 = 0 ∨ left.1 + left.2 ≤ right.1 ∨ right.1 + right.2 ≤ left.1

/-- Every buffer is 8-byte aligned and ends at or below the embedded data, and no two overlap. -/
abbrev LayoutValid (layout : Layout) (sizes : Sizes) (image : Image) : Prop :=
  (∀ buffer ∈ layoutBuffers layout sizes,
    buffer.1 % 8 = 0 ∧ buffer.1 + buffer.2 ≤ dataBase image) ∧
  (layoutBuffers layout sizes).Pairwise DisjointBuffers

/-- An image within the size bound whose layout fits below its data. -/
abbrev Image.Valid (image : Image) (sizes : Sizes) (layout : Layout) : Prop :=
  image.byteSize < MAX_PROGRAM_BYTES ∧ LayoutValid layout sizes image

/-! ### Memory -/

/-- Fresh registers and memory, all zero, with `PC` at the first instruction. -/
def initialMachine : MachineState := { regs := fun _ => 0, mem := fun _ => 0, pc := 0x1000 }

/-- `bytes` bytes at `address` lie entirely in memory. -/
def rangeValid (address : BitVec 64) (bytes : Nat) : Bool :=
  decide (address.toNat + bytes ≤ MEMORY_BYTES)

/-- In memory and aligned to the access size. -/
def accessValid (address : BitVec 64) (bytes : Nat) : Bool :=
  rangeValid address bytes && decide (address.toNat % bytes = 0)

/-- The `n` bytes at `address`, least significant first. -/
def readBuffer (state : MachineState) (address n : Nat) : Bytes n :=
  BitVec.ofNat (8 * n)
    (∑ i ∈ Finset.range n, (state.getByte (BitVec.ofNat 64 (address + i))).toNat * 2 ^ (8 * i))

/-! ### Decoding -/

/-- The 32-bit, `W`-suffixed register operations the upstream decoder lacks: `ADDW` to `REMUW`. -/
inductive WordOp where
  | add | sub | sll | srl | sra | mul | div | divu | rem | remu
  deriving DecidableEq

/-- A decoded instruction: one from the upstream model, or a word operation it lacks. -/
inductive Instruction where
  | base (instruction : Instr)
  | word (op : WordOp) (rd rs1 rs2 : Reg)
  | sraiw (rd rs1 : Reg) (shift : BitVec 5)

/-- Decode one 32-bit encoding: `ECALL` and `EBREAK` exactly, the W-suffixed operations and
`SRAIW`, then the upstream decoder. Other SYSTEM encodings, the CSR instructions, do not decode;
assembler pseudo-instructions have no encoding. -/
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
    return .base (← decode word)

/-- The 32-bit result of a `W` operation: shifts use the low five bits of `b`; division by zero
gives all ones and remainder by zero gives `a`, as RISC-V specifies. -/
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

/-- Every data access is bounds- and alignment-checked; address zero is an ordinary valid
address. -/
def memoryArgumentsValid (state : MachineState) (instruction : Instr) : Bool :=
  match memAccess state instruction with
  | some (address, width, _) => accessValid address width
  | none => true

/-- One ordinary instruction. Of the first two arms only `EBREAK` is reachable: `execute` handles
`ECALL` first, and `decodeInstruction` never produces CSR or pseudo-instructions. They are listed
so this does not depend on that. -/
def ordinaryStep (state : MachineState) : Instruction → Option MachineState
  | .base .ECALL | .base .EBREAK | .base (.CSRS _ _) => none
  | .base (.LI _ _) | .base (.MV _ _) | .base .NOP => none
  | .base instruction =>
      if memoryArgumentsValid state instruction then some (execInstrBr state instruction) else none
  | .word op rd rs1 rs2 =>
      let value := wordResult op ((state.getReg rs1).truncate 32) ((state.getReg rs2).truncate 32)
      some ((state.setReg rd (value.signExtend 64)).setPC (state.pc + 4))
  | .sraiw rd rs shift =>
      let value := ((state.getReg rs).truncate 32).sshiftRight shift.toNat
      some ((state.setReg rd (value.signExtend 64)).setPC (state.pc + 4))

/-- Multiplication, division, and remainder instructions cost four cycles; every other ordinary
instruction costs one. `ECALL` is priced in `execute`. -/
def instructionCycles : Instruction → Nat
  | .base (.MUL ..) | .base (.MULH ..) | .base (.MULHSU ..) | .base (.MULHU ..)
  | .base (.DIV ..) | .base (.DIVU ..) | .base (.REM ..) | .base (.REMU ..) => 4
  | .word .mul .. | .word .div .. | .word .divu .. | .word .rem .. | .word .remu .. => 4
  | _ => 1

/-- The instruction at `PC`: code starts at `0x1000`, four bytes per instruction. -/
def fetch (image : Image) (state : MachineState) : Option Instruction :=
  if 0x1000 ≤ state.pc.toNat ∧ state.pc.toNat % 4 = 0 then
    match image.code[(state.pc.toNat - 0x1000) / 4]? with
    | some word => decodeInstruction word
    | none => none
  else none

/-! ### HASH -/

/-- HASH reads whole 64-byte blocks: both addresses are 8-byte aligned, the byte length is a
nonzero multiple of 64, and input and output lie in memory. -/
def hashArgumentsValid (state : MachineState) : Bool :=
  let source := state.getReg .x10
  let bytes := (state.getReg .x11).toNat
  let destination := state.getReg .x12
  decide (source.toNat % 8 = 0) && decide (0 < bytes ∧ bytes % 64 = 0) &&
    rangeValid source bytes && decide (destination.toNat % 8 = 0) && rangeValid destination 32

/-- The `a1` bytes at address `a0`, least significant first, as `a1 / 64` blocks. -/
def hashInput (state : MachineState) : Query :=
  let n := (state.getReg .x11).toNat / 64 - 1
  ⟨n, readBuffer state (state.getReg .x10).toNat (64 * (n + 1))⟩

/-- Write the 32-byte answer at `a2`, little-endian, and advance `PC`. -/
def writeHash (state : MachineState) (answer : BitVec 256) : MachineState :=
  (state.writeWords (state.getReg .x12)
    [answer.extractLsb' 0 64, answer.extractLsb' 64 64,
      answer.extractLsb' 128 64, answer.extractLsb' 192 64]).setPC (state.pc + 4)

/-! ### Execution and costs -/

/-- How a run ended: `HALT` with exit code 0; any fault or nonzero exit code; or still running
when the step limit was reached. -/
inductive Exit where
  | success | failure | unfinished
  deriving DecidableEq

/-- A finished or cut-off run with its final state, cycles, and compressions. Hash calls are not
counted here; the security experiment counts them at the oracle. -/
structure Execution where
  exit : Exit
  state : MachineState
  cycles : Nat
  compressions : Nat

/-- Add one instruction's cycles and compressions. -/
def Execution.charge (result : Execution) (cycles blocks : Nat) : Execution :=
  { result with cycles := cycles + result.cycles, compressions := blocks + result.compressions }

/-- Run at most `steps` instructions from `state`, answering each HASH by querying `H`. A program
still running after `steps` instructions is reported `unfinished`; since every step costs at least
one cycle, `Termination` rules that out within `CYCLE_LIMIT` steps. -/
def execute (image : Image) : Nat → MachineState → OracleComp HashSpec Execution
  | 0, state => pure { exit := .unfinished, state := state, cycles := 0, compressions := 0 }
  | steps + 1, state =>
    match fetch image state with
    | none => pure { exit := .failure, state := state, cycles := 0, compressions := 0 }
    | some (.base .ECALL) =>
      if state.getReg .x5 = 0 && hashArgumentsValid state then do
        let input := hashInput state
        let answer ← HashSpec.query input
        let result ← execute image steps (writeHash state answer)
        return result.charge (8 * input.blocks) input.blocks
      else if state.getReg .x5 = 1 then
        pure { exit := if state.getReg .x10 = 0 then .success else .failure, state := state,
               cycles := 1, compressions := 0 }
      else pure { exit := .failure, state := state, cycles := 1, compressions := 0 }
    | some instruction =>
      match ordinaryStep state instruction with
      | none => pure { exit := .failure, state := state, cycles := 1, compressions := 0 }
      | some next => do
          let result ← execute image steps next
          return result.charge (instructionCycles instruction) 0

end SigGolf.Riscv
