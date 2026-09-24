import SigGolfCandidate.SphincsCommitment
import SigGolfCandidate.Serialization
import SigGolfCandidate.Hypertree.SecurityPacking

/-!
# Byte-string oracle bridge

The abstract SPHINCS scheme queries lists of `UInt8`. The organizer's RISC-V
oracle queries length-tagged bit vectors. This module fixes their common
little-endian serialization before relating any bytecode HASH instruction to
an abstract scheme call.
-/

namespace SigGolfCandidate.SphincsBridge
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity OracleComp

def toQuery (input : HashInput) : Query :=
  Hypertree.Reference.packed (input.map UInt8.toBitVec)

def adaptOracle (hash : Hash) : SphincsSecurity.HashInput → SphincsSecurity.HashOutput :=
  fun input => hash (toQuery input)

/-- The scheme's fixed-width encoding and the organizer's buffer encoding have the same bytes. -/
theorem bytesLE_eq_vmBytes (n : Nat) (value : BitVec (8 * n)) :
    (bytesLE n value).map UInt8.toBitVec = SigGolf.bytes value := by
  apply List.ext_getElem
  · simp [bytesLE, SigGolf.bytes]
  · intro i hi hj
    simp [bytesLE, SigGolf.bytes, List.getElem_ofFn, List.getElem_map,
      List.getElem_range]

/-- The scheme's `n` serialized bytes become exactly its `8n`-bit oracle query. -/
theorem toQuery_bytesLE (n : Nat) (value : BitVec (8 * n)) :
    toQuery (bytesLE n value) = ⟨8 * n, value⟩ := by
  rw [toQuery, bytesLE_eq_vmBytes]
  exact Serialization.packed_bytes n value

/-- The VM's length-tagged query loses no scheme input bytes. -/
theorem toQuery_injective : Function.Injective toQuery := by
  intro first second h
  have hbytes := Hypertree.SecurityPacking.packed_injective h
  exact (List.map_injective_iff.mpr (fun _ _ heq => UInt8.toBitVec_inj.mp heq)) hbytes

/-- Domain separation survives the conversion to organizer oracle queries. -/
theorem commitmentQuery_ne_tweakable (pk : SphincsSecurity.PublicKey)
    (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    toQuery (SphincsWire.commitmentInput pk) ≠
      toQuery (tweakableHashInput parameter domain payload) := by
  intro h
  exact SphincsWire.commitmentInput_ne_tweakableHashInput pk parameter domain payload
    (toQuery_injective h)

theorem commitmentQuery_ne_keygen (pk : SphincsSecurity.PublicKey)
    (parameter : PublicParameter) (domain : KeygenDomain) (seed : MasterSeed) :
    toQuery (SphincsWire.commitmentInput pk) ≠
      toQuery (keygenHashInput parameter domain seed) := by
  intro h
  exact SphincsWire.commitmentInput_ne_keygenHashInput pk parameter domain seed
    (toQuery_injective h)

theorem commitmentQuery_ne_randomizer (pk : SphincsSecurity.PublicKey)
    (parameter : PublicParameter) (seed : MasterSeed) (message : SphincsSecurity.Message)
    (trial : BitVec 32) :
    toQuery (SphincsWire.commitmentInput pk) ≠
      toQuery (randomizerHashInput parameter seed message trial) := by
  intro h
  exact SphincsWire.commitmentInput_ne_randomizerHashInput pk parameter seed message trial
    (toQuery_injective h)

/-- State at the commitment HASH instruction, before the oracle is called. -/
structure CommitmentReady (state : MachineState) (pk : SphincsSecurity.PublicKey) : Prop where
  source : state.getReg .x10 = 0x40000
  bits : state.getReg .x11 = 480
  destination : state.getReg .x12 = 0x42000
  service : state.getReg .x5 = 1
  input : ∀ i, (hi : i < (SphincsWire.commitmentInput pk).length) →
    state.getByte (BitVec.ofNat 64 (0x40000 + i)) =
      ((SphincsWire.commitmentInput pk).map UInt8.toBitVec)[i]'(by simpa using hi)

/-- A prepared commitment instruction makes the exact abstract commitment query. -/
theorem commitmentReady_hashInput (state : MachineState) (pk : SphincsSecurity.PublicKey)
    (ready : CommitmentReady state pk) :
    hashInput state = toQuery (SphincsWire.commitmentInput pk) := by
  apply Serialization.hashInput_of_list state 0x40000
    ((SphincsWire.commitmentInput pk).map UInt8.toBitVec)
  · exact ready.source
  · rw [ready.bits, List.length_map, SphincsWire.commitmentInput_length]
    rfl
  · intro i hi
    exact ready.input i (by simpa using hi)

/-- The exact HASH call is valid and charges one compression, hence eight cycles. -/
theorem commitmentReady_hashCost (state : MachineState) (pk : SphincsSecurity.PublicKey)
    (ready : CommitmentReady state pk) :
    hashArgumentsValid state = true ∧ compressions (hashInput state).1 = 1 := by
  constructor
  · simp [hashArgumentsValid, ready.source, ready.bits, ready.destination,
      accessValid, rangeValid, MEMORY_BYTES]
  · rw [commitmentReady_hashInput state pk ready]
    simp [toQuery, Hypertree.Reference.packed,
      SphincsWire.commitmentInput_length, compressions]

/-- info: 'SigGolfCandidate.SphincsBridge.toQuery_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms toQuery_injective

/-- info: 'SigGolfCandidate.SphincsBridge.commitmentReady_hashInput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms commitmentReady_hashInput

end SigGolfCandidate.SphincsBridge
