import SigGolfCandidate.SphincsVerifierHashBytes
import SigGolfCandidate.SphincsSubmission
import SigGolfCandidate.Memory
import RiscvZkvm.Rv64.Logic.MemRegion
import RiscvZkvm.Rv64.Logic.MemRegionWrite

/-!
# Verifier witness loader

The organizer's standard loader places the submitted witness at the address
used by the certified first HASH prefix.
-/

namespace SigGolfCandidate.SphincsVerifierLoader
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierHashBytes
open SigGolfCandidate.SphincsVerifierHashSetup
open SigGolfCandidate.SphincsSubmission
open SigGolfCandidate.SphincsBridge

theorem loaded_witness (publicKey : SigGolf.PublicKey) (message : Message)
    (witness : Bytes SphincsWire.signatureBytes) (state : MachineState)
    (loaded : initialState submission .verify (message, publicKey, witness) = some state)
    (i : Nat) (hi : i < SphincsWire.signatureBytes) :
    state.getByte (BitVec.ofNat 64 (0x22ca0 + i)) =
      witness.extractLsb' (8 * i) 8 := by
  unfold initialState at loaded
  rw [if_pos (admissible.2 .verify)] at loaded
  cases Option.some.inj loaded
  dsimp only [submission, layout, sizes]
  dsimp only [inputBuffers, Riscv.standardLayout, Layout.message,
    Layout.secretKey, Layout.publicKey, Layout.cache, Layout.signature,
    Layout.witness, List.foldl_cons, List.foldl_nil]
  rw [Memory.getByte_setReg]
  rw [show Riscv.witnessBase
    ⟨SphincsWire.signatureBytes, SphincsWire.signatureBytes⟩ = 0x22ca0 by decide]
  exact Memory.write_value_byte _ 0x22ca0 SphincsWire.signatureBytes
    witness i (by decide) (by decide) hi

theorem loaded_publicKey (publicKey : SigGolf.PublicKey) (message : Message)
    (witness : Bytes SphincsWire.signatureBytes) (state : MachineState)
    (loaded : initialState submission .verify (message, publicKey, witness) = some state)
    (i : Nat) (hi : i < 16) :
    state.getByte (BitVec.ofNat 64 (0x40 + i)) =
      publicKey.extractLsb' (8 * i) 8 := by
  unfold initialState at loaded
  rw [if_pos (admissible.2 .verify)] at loaded
  cases Option.some.inj loaded
  dsimp only [submission, layout, sizes]
  dsimp only [inputBuffers, Riscv.standardLayout, Layout.message,
    Layout.secretKey, Layout.publicKey, Layout.cache, Layout.signature,
    Layout.witness, List.foldl_cons, List.foldl_nil]
  rw [Memory.getByte_setReg]
  rw [show Riscv.witnessBase
    ⟨SphincsWire.signatureBytes, SphincsWire.signatureBytes⟩ = 0x22ca0 by decide]
  rw [Memory.write_preserves_byte _ 0x22ca0 (bytes witness) 0x40 i
    (by decide)
    (by rw [Memory.bytes_length (n := SphincsWire.signatureBytes)]; decide)
    (by omega) (by left; omega)]
  exact Memory.write_value_byte _ 0x40 16 publicKey i
    (by decide) (by decide) hi

private theorem getByte_word (state : MachineState) (base i : Nat)
    (aligned : base % 8 = 0) (bound : base + i < 2 ^ 64) :
    state.getByte (BitVec.ofNat 64 (base + i)) =
      extractByte (state.getMem (BitVec.ofNat 64 (base + 8 * (i / 8))))
        (i % 8) := by
  have small : base < 2 ^ 64 := by omega
  have ha : (BitVec.ofNat 64 base).toNat % 8 = 0 := by
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small] using aligned
  have hb : (BitVec.ofNat 64 base).toNat + i < 2 ^ 64 := by
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small] using bound
  simp only [MachineState.getByte, BitVec.ofNat_add,
    alignToDword_add_ofNat_of_aligned ha hb,
    byteOffset_add_ofNat_of_aligned ha hb]

private theorem extractByte_slice {n : Nat} (value : BitVec n) (i : Nat) :
    extractByte (value.extractLsb' (64 * (i / 8)) 64) (i % 8) =
      value.extractLsb' (8 * i) 8 := by
  ext j hj
  have within : i % 8 * 8 + j < 64 := by omega
  have offset : 64 * (i / 8) + (i % 8 * 8 + j) = 8 * i + j := by omega
  simp [extractByte, within, offset]

theorem loaded_publicKey_word (publicKey : SigGolf.PublicKey)
    (message : Message) (witness : Bytes SphincsWire.signatureBytes)
    (state : MachineState)
    (loaded : initialState submission .verify (message, publicKey, witness) = some state)
    (index : Fin 2) :
    state.getMem (BitVec.ofNat 64 (0x40 + 8 * index.val)) =
      publicKey.extractLsb' (64 * index.val) 64 := by
  apply eq_of_forall_extractByte
  intro byte hbyte
  have h := loaded_publicKey publicKey message witness state loaded
    (8 * index.val + byte) (by have := index.isLt; omega)
  rw [getByte_word state 0x40 (8 * index.val + byte)
    (by decide) (by omega)] at h
  have quotient : (8 * index.val + byte) / 8 = index.val := by omega
  have remainder : (8 * index.val + byte) % 8 = byte := by omega
  simp only [quotient, remainder] at h
  rw [h]
  symm
  simpa only [quotient, remainder] using
    extractByte_slice publicKey (8 * index.val + byte)

/-- info: 'SigGolfCandidate.SphincsVerifierLoader.loaded_publicKey_word' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms loaded_publicKey_word

/-- The submitted witness begins with the internal root and public parameter. -/
structure EncodedWitness (witness : Bytes SphincsWire.signatureBytes)
    (inner : SphincsSecurity.PublicKey) : Prop where
  root : ∀ i, (hi : i < 20) →
    witness.extractLsb' (8 * i) 8 = inner.root.extractLsb' (8 * i) 8
  parameter : ∀ i, (hi : i < 20) →
    witness.extractLsb' (8 * (20 + i)) 8 =
      inner.parameter.extractLsb' (8 * i) 8

theorem loaded_prefix (publicKey : SigGolf.PublicKey) (message : Message)
    (witness : Bytes SphincsWire.signatureBytes)
    (inner : SphincsSecurity.PublicKey) (state : MachineState)
    (loaded : initialState submission .verify (message, publicKey, witness) = some state)
    (encoded : EncodedWitness witness inner) :
    WitnessPrefix state inner := by
  constructor
  · intro i hi
    rw [loaded_witness publicKey message witness state loaded i (by
      have length := SphincsWire.signatureBytes_eq
      omega)]
    exact encoded.root i hi
  · intro i hi
    have address : 0x22cb4 + i = 0x22ca0 + (20 + i) := by omega
    rw [address, loaded_witness publicKey message witness state loaded
      (20 + i) (by
        have length := SphincsWire.signatureBytes_eq
        omega)]
    exact encoded.parameter i hi

theorem firstHash_ready_loaded (publicKey : SigGolf.PublicKey) (message : Message)
    (witness : Bytes SphincsWire.signatureBytes)
    (inner : SphincsSecurity.PublicKey) (state : MachineState)
    (loaded : initialState submission .verify (message, publicKey, witness) = some state)
    (encoded : EncodedWitness witness inner) :
    SphincsBridge.CommitmentReady (firstHashState state) inner :=
  firstHash_ready state inner
    (loaded_prefix publicKey message witness inner state loaded encoded)

private theorem loaded_pc (publicKey : SigGolf.PublicKey) (message : Message)
    (witness : Bytes SphincsWire.signatureBytes) (state : MachineState)
    (loaded : initialState submission .verify (message, publicKey, witness) = some state) :
    state.pc = 0x1000 := by
  obtain ⟨initial, same, pc⟩ := initialState_exists submission admissible
    .verify (message, publicKey, witness)
  rw [loaded] at same
  cases Option.some.inj same
  exact pc

/-- The loaded verifier reaches its first commitment HASH with exact bytes and cost. -/
theorem loaded_firstHash_executes (hash : Hash) (publicKey : SigGolf.PublicKey)
    (message : Message) (witness : Bytes SphincsWire.signatureBytes)
    (inner : SphincsSecurity.PublicKey) (state : MachineState)
    (loaded : initialState submission .verify (message, publicKey, witness) = some state)
    (encoded : EncodedWitness witness inner)
    (steps : Nat) (result : Execution)
    (tail : Executes hash SphincsImages.verify
      (writeHash (firstHashState state)
        (hash (toQuery (SphincsWire.commitmentInput inner)))) steps result) :
    Executes hash SphincsImages.verify state ((steps + 1) + 73)
      ((result.charge 8 1 1).charge 73 0 0) := by
  exact firstHash_executes hash state inner
    (loaded_pc publicKey message witness state loaded)
    (firstHash_ready_loaded publicKey message witness inner state loaded encoded)
    steps result tail

/-- info: 'SigGolfCandidate.SphincsVerifierLoader.loaded_firstHash_executes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms loaded_firstHash_executes

end SigGolfCandidate.SphincsVerifierLoader
