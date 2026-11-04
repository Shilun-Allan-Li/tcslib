/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Simulate
import TCSlib.Cryptography.Pseudorandom.Functions.OracleAdversary

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Bridge: query trees are one-oracle computations

The concrete layer's adaptive oracle adversaries are `QueryTree I O α`. A tree either returns, or
asks the oracle a question in `I` and continues on the answer in `O`. That is the `Games`
framework's oracle computation over a single oracle. This file builds the translation both ways,
proves it a bijection, and shows that it respects the three operations of the concrete layer:
- running against an oracle function (`QueryTree.eval`) is evaluating the computation with that
  function (`OracleComp.evalFn`), which is also its simulation by a deterministic stateless
  implementation;
- Garg's `QueryTree.simulate` (answer each query by asking `π x` of a new oracle and
  post-processing with `ans x`) is the framework's `simulate` with the corresponding
  implementation;
- the query bound `QueryTree.BoundedBy` is the framework's `CostBoundedBy` with every query
  costing one.

So the concrete layer's results on oracle adversaries (PRF hybrids, GGM, lazy sampling) apply to
one-oracle computations of the framework.

**Disclosure.** `QueryTree.simulate` has no published equations for its two cases; the proof of
`toComp_simulate` reads them by `rfl`. `eval` and `BoundedBy` are read through their published
`@[simp]` equations.

## Main definitions

* `Games.singleSpec I O`: one oracle with queries `I` and answers `O`.
* `Games.Bridge.QueryTree.toComp`, `Games.Bridge.OracleComp.toTree`, `Games.Bridge.treeEquiv`:
  the translation and its inverse.
* `Games.OracleComp.evalFn f c`: the output of `c` when every query is answered by the function
  `f`.
* `Games.Bridge.treeImpl π ans`: the implementation corresponding to `QueryTree.simulate π ans`.

## Main results

* `Games.Bridge.evalFn_toComp`: evaluation is preserved.
* `Games.simulate_ofComp_pure`: simulating with a deterministic stateless implementation is
  evaluation.
* `Games.Bridge.toComp_simulate`: Garg's simulation is the framework's.
* `Games.Bridge.costBoundedBy_toComp_iff`: query bounds are preserved.

## References

* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley, draft of
  22 January 2026, Definition 3.9 (oracle adversaries).
* [VCVio] D. Tuma and the VCVio contributors, *VCVio: machine-checked cryptographic proofs in
  Lean*, https://github.com/dtumad/VCV-io, commit 9054989327a7185ff19ef9ff0f119cccea479501
  (2026-11-04), Apache License 2.0. Design adapted (no code transcribed): oracle specifications
  indexed by a type of oracle names (`VCVio/OracleComp/OracleSpec.lean`), oracle computations as
  a free monad over them (`OracleComp.lean`, `OracleQuery.lean`), and simulation of oracles by
  stateful handlers with query logging (`SimSemantics/`, `QueryTracking/LoggingOracle`).
-/

namespace TCSlib.Cryptography.Games

variable {ι : Type} {I O I' O' α σ : Type}

/-- A single oracle with queries in `I` and answers in `O`. -/
abbrev singleSpec (I O : Type) : OracleSpec Unit := ⟨fun _ => I, fun _ => O⟩

/-- The output of `c` when every query `x` to oracle `i` is answered by `f i x`. -/
def OracleComp.evalFn {spec : OracleSpec ι} (f : ∀ i, spec.dom i → spec.rng i) :
    OracleComp spec α → α
  | .pure a => a
  | .query i x k => evalFn f (k (f i x))

/-- **Deterministic implementations evaluate:** simulating `c` with the stateless implementation
that answers by the function `f` returns `c`'s output under `f` and leaves the state unchanged. -/
theorem simulate_ofComp_pure {ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    (f : ∀ i, spec.dom i → spec.rng i) (c : OracleComp spec α) (s : σ) :
    simulate (QueryImpl.ofComp (σ := σ) (spec' := spec') fun i x => .pure (f i x)) c s =
      .pure (c.evalFn f, s) := by
  induction c with
  | pure a => rfl
  | query i x k ih => exact ih (f i x)

namespace Bridge

/-- A query tree as a one-oracle computation. -/
def QueryTree.toComp : TCSlib.Cryptography.QueryTree I O α → OracleComp (singleSpec I O) α
  | .ret a => .pure a
  | .query x k => .query () x (fun o => toComp (k o))

/-- A one-oracle computation as a query tree. -/
def OracleComp.toTree : OracleComp (singleSpec I O) α → TCSlib.Cryptography.QueryTree I O α
  | .pure a => .ret a
  | .query () x k => .query x (fun o => toTree (k o))

/-- Translating a tree to a computation and back gives the tree. -/
theorem toTree_toComp (t : TCSlib.Cryptography.QueryTree I O α) :
    OracleComp.toTree (QueryTree.toComp t) = t := by
  induction t with
  | ret a => rfl
  | query x k ih => simp only [QueryTree.toComp, OracleComp.toTree, ih]

/-- Translating a one-oracle computation to a tree and back gives the computation. -/
theorem toComp_toTree (c : OracleComp (singleSpec I O) α) :
    QueryTree.toComp (OracleComp.toTree c) = c := by
  induction c with
  | pure a => rfl
  | query i x k ih => cases i; simp only [OracleComp.toTree, QueryTree.toComp, ih]

/-- **Query trees are one-oracle computations:** the translation is a bijection. -/
def treeEquiv : TCSlib.Cryptography.QueryTree I O α ≃ OracleComp (singleSpec I O) α where
  toFun := QueryTree.toComp
  invFun := OracleComp.toTree
  left_inv := toTree_toComp
  right_inv := toComp_toTree

/-- **Evaluation is preserved:** running a tree against the oracle `f` is evaluating its
computation with `f`. -/
theorem evalFn_toComp (f : I → O) (t : TCSlib.Cryptography.QueryTree I O α) :
    (QueryTree.toComp t).evalFn (fun _ => f) = t.eval f := by
  induction t with
  | ret a => rfl
  | query x k ih => simp only [QueryTree.toComp, OracleComp.evalFn, ih,
      TCSlib.Cryptography.QueryTree.eval_query]

/-- The implementation corresponding to `QueryTree.simulate π ans`: a query `x` is answered by
asking `π x` of the new oracle and returning `ans x` of the answer; no state is used. -/
def treeImpl (π : I → I') (ans : I → O' → O) : QueryImpl (singleSpec I O) σ (singleSpec I' O') :=
  QueryImpl.ofComp fun _ x => (OracleComp.call () (π x)).bind fun o' => .pure (ans x o')

/-- **Garg's simulation is the framework's:** the tree `t.simulate π ans` is the framework's
simulation of `t`'s computation by `treeImpl π ans`, with the (unchanged) state dropped.

**Proof sketch.** Induction on `t`; at a query both sides ask `π x` and continue on `ans x` of the
answer. -/
theorem toComp_simulate (π : I → I') (ans : I → O' → O) (t : TCSlib.Cryptography.QueryTree I O α)
    (s : σ) :
    QueryTree.toComp (t.simulate π ans) =
      (simulate (treeImpl π ans) (QueryTree.toComp t) s).bind fun p => .pure p.1 := by
  induction t with
  | ret a => rfl
  | query x k ih =>
    show OracleComp.query () (π x) (fun o' => QueryTree.toComp ((k (ans x o')).simulate π ans)) = _
    simp only [QueryTree.toComp, simulate_query, treeImpl, QueryImpl.ofComp, ih,
      OracleComp.bind_assoc, OracleComp.pure_bind]
    rfl

/-- **Query bounds are preserved:** a tree makes at most `q` queries exactly when its computation
is cost-bounded by `q` with every query costing one. -/
theorem costBoundedBy_toComp_iff (t : TCSlib.Cryptography.QueryTree I O α) (q : ℕ) :
    (QueryTree.toComp t).CostBoundedBy (fun _ => 1) q ↔ t.BoundedBy q := by
  induction t generalizing q with
  | ret a => simp [QueryTree.toComp]
  | query x k ih =>
    cases q with
    | zero => simp [QueryTree.toComp, OracleComp.costBoundedBy_query]
    | succ q =>
      simp only [QueryTree.toComp, OracleComp.costBoundedBy_query,
        TCSlib.Cryptography.QueryTree.boundedBy_query_succ, Nat.add_sub_cancel, ih]
      simp

end Bridge

end TCSlib.Cryptography.Games
