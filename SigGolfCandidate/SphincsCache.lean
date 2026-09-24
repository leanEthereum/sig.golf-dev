import SigGolfCandidate.SphincsWire
import SigGolf.Riscv

/-!
# Public cache layout

The key generator stores the top XMSS tree level by level. The signer reads
authentication siblings from these rows, starting with the 2,048 leaves.
The 128 KiB buffer has a 40-byte header and 4,095 twenty-byte nodes.
-/

namespace SigGolfCandidate.SphincsCache
open SphincsSecurity SigGolfCandidate.SphincsWire SigGolf

def headerBytes : Nat := 2 * digestBytes
def topLeaves : Nat := 2 ^ maxLayerHeight
def treeNodes : Nat := 2 * topLeaves - 1
def usedBytes : Nat := headerBytes + treeNodes * digestBytes

theorem usedBytes_eq : usedBytes = 81940 := by decide
theorem usedBytes_le_capacity : usedBytes ≤ CACHE_BYTES := by
  rw [usedBytes_eq]
  decide

/-- Row zero holds leaves; row eleven holds the root. -/
def rowBase (level : Nat) : Nat :=
  headerBytes + digestBytes *
    (2 ^ (maxLayerHeight + 1) - 2 ^ (maxLayerHeight + 1 - level))

def nodeOffset (level node : Nat) : Nat :=
  rowBase level + digestBytes * node

/-- The next row starts exactly after this row's nodes. -/
theorem rowBase_next (level : Nat) (hl : level < maxLayerHeight) :
    rowBase (level + 1) = rowBase level +
      digestBytes * 2 ^ (maxLayerHeight - level) := by
  have hl' : level < 11 := by simpa [maxLayerHeight] using hl
  interval_cases level <;>
    decide

/-- Every node, including the top root, is wholly inside the used cache prefix. -/
theorem nodeOffset_end_le_usedBytes (level node : Nat)
    (hl : level ≤ maxLayerHeight) (hn : node < 2 ^ (maxLayerHeight - level)) :
    nodeOffset level node + digestBytes ≤ usedBytes := by
  have hl' : level ≤ 11 := by simpa [maxLayerHeight] using hl
  interval_cases h : level <;>
    simp [nodeOffset, rowBase, usedBytes, headerBytes, treeNodes,
      topLeaves, maxLayerHeight, digestBytes] at hl hn ⊢ <;> omega

theorem rootOffset_eq : rowBase maxLayerHeight = 81920 := by decide
theorem rootEndsAtUsedBytes : rowBase maxLayerHeight + digestBytes = usedBytes := by decide

/-- info: 'SigGolfCandidate.SphincsCache.nodeOffset_end_le_usedBytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms nodeOffset_end_le_usedBytes

end SigGolfCandidate.SphincsCache
