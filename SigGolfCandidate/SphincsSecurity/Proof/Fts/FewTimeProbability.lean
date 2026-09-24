import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Fts.FewTimeWitness
/-!
# Probability of a fixed few-time coverage pattern

The relevant part of an admissible digest is its 34-bit index and its twenty opened 8-bit leaf
coordinates.  For a fixed assignment of trees to distinct signing results, the successful tuples
are in bijection with one free index and one free leaf vector per signing result.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

abbrev FewTimeView := Index × (FtsTree → FtsLeaf)

theorem fewTimeView_card : Fintype.card FewTimeView =
    2 ^ (totalHeight + ftsTreeHeight * (ftsTrees - 1)) := by
  simp only [FewTimeView, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    Index, FtsTree, FtsLeaf]
  rw [← pow_mul, ← pow_add]

noncomputable local instance instSampleableTypeOfFintypeOfNonempty_sphincsSecurity {R : Type} [Fintype R] [Nonempty R] : SampleableType R :=
  SampleableType.ofFintype R

end SphincsSecurity.Concrete
