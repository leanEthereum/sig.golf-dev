import SigGolfCandidate.SphincsVerifierHashBytes
import SigGolfCandidate.SphincsSubmission
import SigGolfCandidate.Memory

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
