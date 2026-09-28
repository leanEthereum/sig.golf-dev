import SigGolf.Parameters
import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
import VCVio.OracleComp.QueryTracking.WriterCost
import VCVio.OracleComp.Constructions.SampleableType
import VCVio.EvalDist.BitVec

/-! # Oracle

The random oracle `H` that every program and the adversary share, and its two readings: sampled
lazily, so each new input gets an independent uniform answer, or fixed to one function, so a
statement can hold for every `H`. In VCVio's vocabulary, an `OracleComp HashSpec α` is a
computation that may query `H`, a `ProbComp α` is one that may flip coins, and
`evalWithAnswerFn f` runs a computation with every query answered by the function `f`. Two
notations appear throughout: `$ᵗ T` draws a uniform element of `T`, and `Pr[p | c]` is the
probability that computation `c` returns a value satisfying `p`. -/

namespace SigGolf
open OracleSpec OracleComp

/-- Byte strings of one or more 64-byte blocks, as HASH reads them: `⟨n, bytes⟩` holds `n + 1` blocks.
The length is part of the input; there is no implicit domain separation. -/
abbrev Query := (n : Nat) × Bytes (64 * (n + 1))

/-- The number of 64-byte blocks in an oracle input, which is also its compression count. -/
def Query.blocks (query : Query) : Nat := query.1 + 1

/-- The hash oracle's signature: block inputs to 32-byte answers. `withRandomOracle` answers uniformly at random; `Hash` fixes one function. -/
abbrev HashSpec : OracleSpec Query := Query →ₒ BitVec 256

/-- One fixed oracle, for statements that must hold for every H. -/
abbrev Hash := QueryImpl HashSpec Id

/-- The security experiment's oracles: private coins and the shared hash. -/
abbrev World := unifSpec + HashSpec

/-- One shared lazy random oracle. Repeated inputs receive the same answer. -/
noncomputable def withRandomOracle {α : Type} (program : OracleComp HashSpec α) : ProbComp α :=
  (simulateQ (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp)) program).run' ∅

/-- The security experiment's shared oracles: private coins forwarded for free, and the same lazy random oracle, where every hash call, cache hits included, costs one. -/
noncomputable def countedOracle :=
  (unifFwdImpl HashSpec + (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))).withAddCost
    (fun | .inl _ => (0 : Nat) | .inr _ => 1)

/-- A uniform 32-byte secret key. -/
noncomputable def sampleSecretKey : ProbComp SecretKey := $ᵗ SecretKey

end SigGolf
