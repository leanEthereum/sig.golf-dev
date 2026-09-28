import Solution

/-! Run by the verifier after the proof has been checked: evaluates the four images of the
verified submission and writes each as raw bytes under `.lake/images`, `<program>.code` holding
the instruction words little-endian and `<program>.data` the data bytes. A submission whose
images cannot be evaluated is rejected. -/

namespace SigGolf.Extract

/-- The low `n` bytes of a bit vector, least significant first. -/
def bytesOf {w : Nat} (value : BitVec w) (n : Nat) : ByteArray :=
  ⟨(Array.range n).map fun i => UInt8.ofNat ((value >>> (8 * i)).toNat % 256)⟩

def write (folder : System.FilePath) (name : String) (image : SigGolf.Riscv.Image) : IO Unit := do
  let code := image.code.foldl (fun acc word => acc ++ bytesOf word 4) ByteArray.empty
  let data := ⟨(image.data.map fun byte => UInt8.ofNat byte.toNat).toArray⟩
  IO.FS.writeBinFile (folder / (name ++ ".code")) code
  IO.FS.writeBinFile (folder / (name ++ ".data")) data

def run (folder : System.FilePath) : IO Unit := do
  IO.FS.createDirAll folder
  write folder "keygen" (SigGolf.Challenge.submission.image .keygen)
  write folder "sign" (SigGolf.Challenge.submission.image .sign)
  write folder "expand" (SigGolf.Challenge.submission.image .expand)
  write folder "verify" (SigGolf.Challenge.submission.image .verify)

end SigGolf.Extract

#eval SigGolf.Extract.run ".lake/images"
