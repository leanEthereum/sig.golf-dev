import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Fts.FewTimeSignerView
namespace SphincsSecurity.Concrete

open OracleSpec

abbrev DigestLoopRecord :=
  Option (Randomness × Index × (IndexGroup → FtsLeaf)) × QueryCache HashSpec

def selectedLoopView? (result : DigestLoopRecord) : Option FewTimeView :=
  result.1.map (fun selected => selectedFewTimeView selected.2.1 selected.2.2)

end SphincsSecurity.Concrete
