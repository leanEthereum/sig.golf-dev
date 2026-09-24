import SigGolfCandidate.SphincsSecurity.Scheme

/-!
# Candidate wire format

The signature and witness have the same bytes. Both begin with the internal
40-byte public key (`root || parameter`), which the verifier binds to the
competition's 16-byte public key before it checks the SPHINCS path. All words
and digests below are little-endian, matching the random-oracle input format.
-/

namespace SigGolfCandidate.SphincsWire
open SphincsSecurity

def digestBytes : Nat := 20
def counterBytes : Nat := 4
def internalPublicKeyBytes : Nat := 2 * digestBytes
def ftsOpeningBytes : Nat := (1 + ftsTreeHeight) * digestBytes
def layerBytes (lay : Layer) : Nat :=
  counterBytes + numChains * digestBytes + layerHeight lay * digestBytes

def signatureBytes : Nat :=
  internalPublicKeyBytes + digestBytes + (ftsTrees - 1) * ftsOpeningBytes +
    layerBytes topLayer + layerBytes middleLayer + layerBytes middle2Layer +
    layerBytes middle3Layer + layerBytes middle4Layer + layerBytes bottomLayer

theorem signatureBytes_eq : signatureBytes = 11324 := by decide

def rootOffset : Nat := 0
def parameterOffset : Nat := rootOffset + digestBytes
def randomizerOffset : Nat := parameterOffset + digestBytes
def ftsOffset : Nat := randomizerOffset + digestBytes
def topOffset : Nat := ftsOffset + (ftsTrees - 1) * ftsOpeningBytes
def middleOffset : Nat := topOffset + layerBytes topLayer
def middle2Offset : Nat := middleOffset + layerBytes middleLayer
def middle3Offset : Nat := middle2Offset + layerBytes middle2Layer
def middle4Offset : Nat := middle3Offset + layerBytes middle3Layer
def bottomOffset : Nat := middle4Offset + layerBytes middle4Layer

theorem wireEndsAtSignatureBytes : bottomOffset + layerBytes bottomLayer = signatureBytes := by
  decide

/-- A four-byte counter is canonical only when its unused upper twelve bits are zero. -/
def counterWordValid (value : BitVec 32) : Prop := value.toNat < 2 ^ counterBits

theorem encodedCounterValid (value : Counter) :
    counterWordValid (BitVec.ofNat 32 value.toNat) := by
  simp only [counterWordValid, BitVec.toNat_ofNat]
  have h := value.isLt
  simp only [counterBits] at h ⊢
  omega

/-- Tag 13 is distinct from the scheme's keygen, randomizer and verification tags 0–12. -/
def commitmentInput (publicKey : SphincsSecurity.PublicKey) : List UInt8 :=
  fieldBytes (tweakFields 13 0 0 0 0) ++
    bytesLE digestBytes publicKey.root ++ bytesLE digestBytes publicKey.parameter

theorem commitmentInput_length (publicKey : SphincsSecurity.PublicKey) :
    (commitmentInput publicKey).length = 60 := by
  simp [commitmentInput, fieldBytes, tweakFields, bytesLE, digestBytes]

/-- Public key seen by the beta interface: the first 16 oracle-output bytes. -/
def compressedPublicKey (publicKey : SphincsSecurity.PublicKey) :
    OracleComp SphincsSecurity.HashSpec (BitVec 128) := do
  let output ← Concrete.oracleHash (commitmentInput publicKey)
  return output.extractLsb' 0 128

/-- Fixed-width serialization of a vector of 20-byte digests. -/
def digestVectorBytes {n : Nat} (values : Fin n → Digest) : List UInt8 :=
  List.ofFn fun byte : Fin (digestBytes * n) =>
    let digest : Fin n := ⟨byte.val / digestBytes, by
      have h := byte.isLt
      simp only [digestBytes] at h ⊢
      omega⟩
    UInt8.ofBitVec ((values digest).extractLsb' (8 * (byte.val % digestBytes)) 8)

theorem digestVectorBytes_length {n : Nat} (values : Fin n → Digest) :
    (digestVectorBytes values).length = digestBytes * n := by
  simp [digestVectorBytes]

/-- A FORS opening stores its secret followed by its eight authentication nodes. -/
def ftsOpening (signature : Signature) (tree : FtsTree) : List UInt8 :=
  bytesLE digestBytes (signature.ftsSecret tree) ++
    digestVectorBytes (signature.ftsPath tree)

theorem ftsOpening_length (signature : Signature) (tree : FtsTree) :
    (ftsOpening signature tree).length = ftsOpeningBytes := by
  simp only [ftsOpening, List.length_append, digestVectorBytes_length]
  simp [bytesLE, ftsOpeningBytes, ftsTreeHeight, digestBytes]

/-- Concatenate fixed-width fields without committing to a particular list representation. -/
def concatFields : (n : Nat) → (Fin n → List UInt8) → List UInt8
  | 0, _ => []
  | n + 1, fields => fields 0 ++ concatFields n (fun i => fields i.succ)

theorem concatFields_length : ∀ (n : Nat) (fields : Fin n → List UInt8) (width : Nat),
    (∀ i, (fields i).length = width) → (concatFields n fields).length = n * width := by
  intro n
  induction n with
  | zero => intro fields width _; simp [concatFields]
  | succ n ih =>
      intro fields width h
      simp only [concatFields, List.length_append]
      rw [h 0, ih _ width (fun i => h i.succ)]
      simp [Nat.succ_mul, Nat.add_comm]

/-- The 20-bit counter occupies four bytes so the next digest is aligned. -/
def layerEncoding (signature : Signature) (lay : Layer) : List UInt8 :=
  let part := signature.layers lay
  bytesLE counterBytes (BitVec.ofNat 32 part.counter.toNat) ++
    digestVectorBytes part.chainValues ++ digestVectorBytes part.path

theorem layerEncoding_length (signature : Signature) (lay : Layer) :
    (layerEncoding signature lay).length = layerBytes lay := by
  simp only [layerEncoding, List.length_append, digestVectorBytes_length]
  simp [bytesLE, layerBytes, counterBytes, digestBytes]
  omega

def encodeSignature (publicKey : SphincsSecurity.PublicKey)
    (signature : Signature) : List UInt8 :=
  bytesLE digestBytes publicKey.root ++ bytesLE digestBytes publicKey.parameter ++
    bytesLE digestBytes signature.randomness ++
    concatFields (ftsTrees - 1) (ftsOpening signature) ++
    layerEncoding signature topLayer ++ layerEncoding signature middleLayer ++
    layerEncoding signature middle2Layer ++ layerEncoding signature middle3Layer ++
    layerEncoding signature middle4Layer ++ layerEncoding signature bottomLayer

theorem encodeSignature_length (publicKey : SphincsSecurity.PublicKey)
    (signature : Signature) : (encodeSignature publicKey signature).length = signatureBytes := by
  simp only [encodeSignature, List.length_append, layerEncoding_length]
  rw [concatFields_length _ _ _ (ftsOpening_length signature)]
  simp [bytesLE, signatureBytes, internalPublicKeyBytes, digestBytes]

end SigGolfCandidate.SphincsWire
