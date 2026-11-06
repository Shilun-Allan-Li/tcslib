/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Simulate
import TCSlib.Cryptography.Pseudorandom.Functions.OracleAdversary

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false
attribute [local irreducible] TCSlib.Cryptography.Games.simulate TCSlib.Cryptography.QueryTree.BoundedBy TCSlib.Cryptography.QueryTree.eval TCSlib.Cryptography.QueryTree.induct TCSlib.Cryptography.QueryTree.simulate TCSlib.Cryptography.Games.OracleComp.CostBoundedBy TCSlib.Cryptography.Games.OracleComp.bind TCSlib.Cryptography.Games.OracleComp.call TCSlib.Cryptography.Games.QueryImpl.ofComp

/-!
# Query trees in the framework: evaluation, simulation, query bounds

The concrete layer's adaptive oracle adversaries `QueryTree I O α` *are* the `Games` framework's
computations over a single oracle (`QueryTree` abbreviates `OracleComp (singleSpec I O) α`;
ruling of 2026-11-05, item F-1). This file shows that the concrete layer's three operations on
them are the framework's:
- running against an oracle function (`QueryTree.eval`) is evaluating the computation with that
  function (`OracleComp.evalFn`), which is also its simulation by a deterministic stateless
  implementation;
- Garg's `QueryTree.simulate` (answer each query by asking `π x` of a new oracle and
  post-processing with `ans x`) is the framework's `simulate` with the corresponding
  implementation;
- the query bound `QueryTree.BoundedBy` is the framework's `CostBoundedBy` with every query
  costing one.

So the concrete layer's results on oracle adversaries (PRF hybrids, GGM, lazy sampling) are results
about the framework's one-oracle computations. Before the restatement, this file was bridge B1:
a translation between two types, with its inverse and a bijection. The translation is now the
identity and is gone.

## Main definitions

* `Games.OracleComp.evalFn f c`: the output of `c` when every query is answered by the function
  `f`.
* `Games.Bridge.treeImpl π ans`: the implementation corresponding to `QueryTree.simulate π ans`.

## Main results

* `Games.Bridge.eval_eq_evalFn`: evaluation is the framework's.
* `Games.simulate_ofComp_pure`: simulating with a deterministic stateless implementation is
  evaluation.
* `Games.Bridge.simulate_eq`: Garg's simulation is the framework's.
* `Games.Bridge.costBoundedBy_iff_boundedBy`: query bounds are the framework's.

## References

* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley, draft of
  22 January 2026, Definition 3.9 (oracle adversaries).
* [VCVio] D. Tuma and the VCVio contributors, *VCVio: machine-checked cryptographic proofs in
  Lean*, https://github.com/dtumad/VCV-io, commit 9054989327a7185ff19ef9ff0f119cccea479501
  (2026-11-04), Apache License 2.0. Design adapted (no code transcribed): oracle specifications
  indexed by a type of oracle names (`VCVio/OracleComp/OracleSpec.lean`), oracle computations as
  a free monad over them (`OracleComp.lean`, `OracleQuery.lean`), and simulation of oracles by
  stateful handlers (`SimSemantics/`).
-/

namespace TCSlib.Cryptography.Games

variable {ι : Type} {I O I' O' α σ : Type}

/-- The output of `c` when every query `x` to oracle `i` is answered by `f i x`. -/
def OracleComp.evalFn {spec : OracleSpec ι} (f : ∀ i, spec.dom i → spec.rng i) :
    OracleComp spec α → α
  | .pure a => a
  | .query i x k => evalFn f (k (f i x))

/-- A return evaluates to its value: `(pure a).evalFn f = a`. -/
theorem OracleComp.evalFn_pure {spec : OracleSpec ι} (f : ∀ i, spec.dom i → spec.rng i) (a : α) :
    (OracleComp.pure a : OracleComp spec α).evalFn f = a :=
  rfl

/-- A query evaluates as its continuation on the answer `f i x`:
`(query i x k).evalFn f = (k (f i x)).evalFn f`. -/
theorem OracleComp.evalFn_query {spec : OracleSpec ι} (f : ∀ i, spec.dom i → spec.rng i)
    (i : ι) (x : spec.dom i) (k : spec.rng i → OracleComp spec α) :
    (OracleComp.query i x k).evalFn f = (k (f i x)).evalFn f :=
  rfl

/-- **Deterministic implementations evaluate:** simulating `c` with the stateless implementation
that answers by the function `f` returns `c`'s output under `f` and leaves the state unchanged. -/
theorem simulate_ofComp_pure {ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    (f : ∀ i, spec.dom i → spec.rng i) (c : OracleComp spec α) (s : σ) :
    simulate (QueryImpl.ofComp (σ := σ) (spec' := spec') fun i x => .pure (f i x)) c s =
      .pure (c.evalFn f, s) := by
  induction c with
  | pure a => rw [simulate_pure, OracleComp.evalFn_pure]
  | query i x k ih =>
    rw [simulate_query, QueryImpl.ofComp_apply, OracleComp.pure_bind, OracleComp.pure_bind,
      OracleComp.evalFn_query]
    exact ih (f i x)

namespace Bridge

/-- **Evaluation is the framework's:** running a tree against the oracle `f` is evaluating it, as
a one-oracle computation, with `f`. -/
theorem eval_eq_evalFn (f : I → O) (t : TCSlib.Cryptography.QueryTree I O α) :
    t.eval f = OracleComp.evalFn (fun _ => f) t := by
  induction t using TCSlib.Cryptography.QueryTree.induct with
  | ret a => rw [TCSlib.Cryptography.QueryTree.eval_ret, OracleComp.evalFn_pure]
  | query x k ih =>
    rw [TCSlib.Cryptography.QueryTree.eval_query, OracleComp.evalFn_query]
    exact ih (f x)

/-- The implementation corresponding to `QueryTree.simulate π ans`: a query `x` is answered by
asking `π x` of the new oracle and returning `ans x` of the answer; no state is used. -/
def treeImpl (π : I → I') (ans : I → O' → O) : QueryImpl (singleSpec I O) σ (singleSpec I' O') :=
  QueryImpl.ofComp fun _ x => (OracleComp.call () (π x)).bind fun o' => .pure (ans x o')

/-- The implementation answers the query `x` by asking `π x` and returning `ans x` of the answer,
with the state `s` unchanged:
`treeImpl π ans u x s = query () (π x) (fun o' => pure (ans x o', s))`. -/
theorem treeImpl_apply (π : I → I') (ans : I → O' → O) (u : Unit) (x : I) (s : σ) :
    treeImpl (σ := σ) π ans u x s = OracleComp.query () (π x) fun o' => .pure (ans x o', s) := by
  rw [treeImpl, QueryImpl.ofComp_apply, OracleComp.bind_assoc, OracleComp.call_bind]
  simp only [OracleComp.pure_bind]

/-- **Garg's simulation is the framework's:** the tree `t.simulate π ans` is the framework's
simulation of `t` by `treeImpl π ans`, with the (unchanged) state dropped.

**Proof sketch.** Induction on `t`; at a query both sides ask `π x` and continue on `ans x` of the
answer. -/
theorem simulate_eq (π : I → I') (ans : I → O' → O) (t : TCSlib.Cryptography.QueryTree I O α)
    (s : σ) :
    t.simulate π ans = (simulate (treeImpl π ans) t s).bind fun p => .pure p.1 := by
  induction t using TCSlib.Cryptography.QueryTree.induct with
  | ret a =>
    rw [TCSlib.Cryptography.QueryTree.simulate_ret, simulate_pure, OracleComp.pure_bind]
  | query x k ih =>
    rw [TCSlib.Cryptography.QueryTree.simulate_query, simulate_query, treeImpl_apply]
    simp only [OracleComp.query_bind, OracleComp.pure_bind, ih]

/-- **Query bounds are the framework's:** a tree makes at most `q` queries exactly when it is
cost-bounded by `q` with every query costing one. -/
theorem costBoundedBy_iff_boundedBy (t : TCSlib.Cryptography.QueryTree I O α) (q : ℕ) :
    OracleComp.CostBoundedBy (fun _ => 1) t q ↔ t.BoundedBy q := by
  induction t using TCSlib.Cryptography.QueryTree.induct generalizing q with
  | ret a => simp
  | query x k ih =>
    cases q with
    | zero => simp [OracleComp.costBoundedBy_query]
    | succ q =>
      simp only [OracleComp.costBoundedBy_query,
        TCSlib.Cryptography.QueryTree.boundedBy_query_succ, Nat.add_sub_cancel, ih]
      simp

end Bridge

end TCSlib.Cryptography.Games
