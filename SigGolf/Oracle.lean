import SigGolf.Parameters
import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
import VCVio.OracleComp.QueryTracking.WriterCost

/-! # Oracle

The random oracle `H` that every program and the adversary share, and its readings: sampled
lazily, so each new input gets an independent uniform answer, with or without a running count of
calls; or fixed to one function, so a statement can hold for every `H`.

VCVio vocabulary used here and below. An `OracleComp spec α` is a computation that may query
the oracles in `spec`; `A →ₒ B` specifies one oracle from `A` to `B`, and `spec₁ + spec₂`
offers both, a query being tagged `.inl` or `.inr`. `unifSpec` is the coin oracle and `ProbComp`
is `OracleComp unifSpec`. A `QueryImpl spec m` answers each query of `spec` by a computation in
the monad `m`; for `m = Id` it is just a function from queries to answers. `simulateQ impl c`
runs `c` with every query answered by `impl`, and `evalWithAnswerFn f c` does so for a plain
function `f`. `liftM` embeds a computation over fewer oracles into one over more. Two notations:
`$ᵗ T` draws a uniform element of `T`; `Pr[p | c]` is the probability that `c` returns a
value satisfying `p`, and `Pr[= x | c]` that it returns exactly `x`. Plain Lean, too: `decide p`
is the Boolean value of the proposition `p`, and inside a `do` block `let some x := e | fallback`
continues with `x` when `e` is `some x` and otherwise returns `fallback`. -/

namespace SigGolf
open OracleComp OracleSpec

/-- Byte strings of one or more 64-byte blocks, as HASH reads them: `⟨n, bytes⟩` holds `n + 1`
blocks, the README's `k`, so the empty input is unrepresentable. The length is part of the input;
there is no implicit domain separation. -/
abbrev Query := (n : Nat) × Bytes (64 * (n + 1))

/-- The number of 64-byte blocks in an oracle input, which is also its compression count. -/
def Query.blocks (query : Query) : Nat := query.1 + 1

/-- The hash oracle's signature: block inputs to 32-byte answers. -/
abbrev HashSpec : OracleSpec Query := Query →ₒ BitVec 256

/-- One particular function `H`, for statements that must hold for every `H`. -/
abbrev Hash := QueryImpl HashSpec Id

/-- The security experiment's shared oracles: private coins and the hash. -/
abbrev World := unifSpec + HashSpec

/-- Run against one lazy random oracle: it keeps the answers given so far, draws a fresh uniform
answer for a new input, and repeats the stored one otherwise. Starts with nothing stored. -/
def withRandomOracle {α : Type} (program : OracleComp HashSpec α) : ProbComp α :=
  (simulateQ HashSpec.randomOracle program).run' ∅

/-- One unit per hash call, cache hits included; coins are free. -/
def hashCost : World.Domain → Nat
  | .inl _ => 0
  | .inr _ => 1

/-- The same lazy random oracle, with private coins forwarded for free and a running total of
`hashCost`; running it returns the result paired with the total. -/
def countedOracle : QueryImpl World (AddWriterT Nat (StateT (QueryCache HashSpec) ProbComp)) :=
  (unifFwdImpl HashSpec + HashSpec.randomOracle).withAddCost hashCost

end SigGolf
