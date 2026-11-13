/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.OracleComp

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Implementing oracles: simulation and logging

An oracle computation only *asks* its oracles. A security game decides how they answer: with a
keyed function, with fresh coins on every query (a randomized encryption oracle), refusing some
queries (a CCA2 decryption oracle that will not decrypt the challenge), or by asking other
oracles (a reduction that answers its adversary's queries with queries of its own). All of these
are *implementations*: for each oracle and query, a computation over a target specification that
returns the answer and updates a state. `simulate` runs a computation with every query answered
by an implementation, threading the state.

Logging is an implementation transformer: it answers as before and also appends every query and
its answer to a log kept in the state. Win conditions such as "the forged message was never
queried" are predicates on that log. Logging never changes the computation
(`simulate_withLog`).

## Main definitions

* `Games.QueryImpl spec σ spec'`: implementations of the oracles of `spec` by computations over
  `spec'`, with state `σ`.
* `Games.simulate impl c s`: run `c` from state `s`, answering its queries with `impl`.
* `Games.QueryImpl.ofComp`, `QueryImpl.passthrough`, `QueryImpl.sum`: stateless implementations,
  forwarding queries unchanged, and implementing two oracle families side by side.
* `Games.QueryLog spec`, `Games.QueryImpl.withLog`: the record of a run's queries and answers, and
  the logging transformer.
* `Games.QueryImpl.comp`: answering one implementation's queries with another.

## Main results

* `Games.simulate_bind`: simulation commutes with sequencing.
* `Games.simulate_withLog`: forgetting the log of a logged simulation gives the plain simulation.
* `Games.simulate_comp`: simulation composes; a reduction run against an implementation of its
  oracles is a single implementation of its adversary's oracles.
* `Games.simulate_costBoundedBy`: if each query of `c` to oracle `i` is answered by a computation
  of cost at most `b i`, and `c` is cost-bounded by `q` when oracle `i` costs `b i`, then the
  simulation is cost-bounded by `q`.
* `Games.simulate_costBoundedBy_once`: an implementation whose only costly call (of cost at most
  one) marks the state as used costs at most one query in total.
* `Games.simulate_eq_of_abs`, `Games.simulate_eq_of_abs_bounded`: simulation through an
  abstraction of the state, on every run or along runs with a query budget.

## References

* [VCVio] D. Tuma and the VCVio contributors, *VCVio: machine-checked cryptographic proofs in
  Lean*, https://github.com/dtumad/VCV-io, commit 9054989327a7185ff19ef9ff0f119cccea479501
  (2026-11-04), Apache License 2.0. Design adapted (no code transcribed): oracle specifications
  indexed by a type of oracle names (`VCVio/OracleComp/OracleSpec.lean`), oracle computations as
  a free monad over them (`OracleComp.lean`, `OracleQuery.lean`), probabilistic computations as
  computations over the uniform-selection oracles (`OracleComp/ProbComp/Basic.lean`), and
  simulation of oracles by stateful handlers with query logging and composition (`SimSemantics/`,
  `SimSemantics/QueryImpl/Compose.lean`, `QueryTracking/LoggingOracle`).
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley, draft of
  22 January 2026, Definition 3.9 (answering an adversary's queries in a reduction).
-/

namespace TCSlib.Cryptography.Games

/-! Seal A (dl-folds, cp1): a verbatim copy of `TCSlib/Cryptography/Games/Simulate.lean`, with every seal candidate of its
full TCSlib import closure (9 definitions, `PolyExpr.eval` exempt) irreducible from here on. -/
attribute [local irreducible] _root_.TCSlib.Cryptography.Games.OracleComp.AllOutputs _root_.TCSlib.Cryptography.Games.OracleComp.CostBoundedBy _root_.TCSlib.Cryptography.Games.OracleComp.CostBoundedBy.match_1 _root_.TCSlib.Cryptography.Games.OracleComp.bind _root_.TCSlib.Cryptography.Games.OracleComp.bind.match_1 _root_.TCSlib.Cryptography.Games.OracleComp.call _root_.TCSlib.Cryptography.Games.OracleComp.liftLeft _root_.TCSlib.Cryptography.Games.OracleComp.liftLeft.match_1 _root_.TCSlib.Cryptography.Games.OracleComp.liftRight


variable {ι ι' ι₁ ι₂ : Type} {α β σ : Type}

/-- An **implementation** of the oracles of `spec` by computations over `spec'`, with state `σ`:
on oracle `i`, query `x` and state `s`, a computation returning the answer and the new state.
[VCVio, SimSemantics] -/
abbrev QueryImpl {ι ι' : Type} (spec : OracleSpec ι) (σ : Type) (spec' : OracleSpec ι') : Type :=
  ∀ i, spec.dom i → σ → OracleComp spec' (spec.rng i × σ)

/-- An implementation is a function of the oracle, the query and the state:
`QueryImpl spec σ spec' = ∀ i, spec.dom i → σ → OracleComp spec' (spec.rng i × σ)`. -/
theorem queryImpl_def {ι ι' : Type} (spec : OracleSpec ι) (σ : Type) (spec' : OracleSpec ι') :
    QueryImpl spec σ spec' = ∀ i, spec.dom i → σ → OracleComp spec' (spec.rng i × σ) := rfl

/-- **Simulation:** run `c` from state `s`, answering each of its queries with `impl` and
threading the state; return `c`'s result and the final state. [VCVio, SimSemantics] -/
def simulate {spec : OracleSpec ι} {spec' : OracleSpec ι'} (impl : QueryImpl spec σ spec') :
    OracleComp spec α → σ → OracleComp spec' (α × σ)
  | .pure a, s => .pure (a, s)
  | .query i x k, s => (impl i x s).bind (fun ys => simulate impl (k ys.1) ys.2)

section Simulate

variable {spec : OracleSpec ι} {spec' : OracleSpec ι'} (impl : QueryImpl spec σ spec')

/-- Simulating a return returns it with the state unchanged. -/
@[simp] theorem simulate_pure (a : α) (s : σ) :
    simulate impl (OracleComp.pure a) s = .pure (a, s) := rfl

/-- Simulating a query runs the implementation, then simulates the continuation. -/
@[simp] theorem simulate_query (i : ι) (x : spec.dom i) (k : spec.rng i → OracleComp spec α)
    (s : σ) :
    simulate impl (OracleComp.query i x k) s =
      (impl i x s).bind (fun ys => simulate impl (k ys.1) ys.2) := rfl

/-- **Simulation commutes with sequencing:** simulating `c` followed by `f` is simulating `c`,
then simulating `f` on its result from the state it reached.

**Proof sketch.** Induction on `c`; at a query, both sides run the implementation first, and the
monad's associativity lines up the continuations. -/
theorem simulate_bind (c : OracleComp spec α) (f : α → OracleComp spec β) (s : σ) :
    simulate impl (c.bind f) s = (simulate impl c s).bind (fun p => simulate impl (f p.1) p.2) := by
  induction c generalizing s with
  | pure a => simp only [OracleComp.pure_bind, simulate_pure]
  | query i x k ih => simp only [OracleComp.query_bind, simulate_query, OracleComp.bind_assoc, ih]

/-- Simulating a single call is running the implementation. -/
theorem simulate_call (i : ι) (x : spec.dom i) (s : σ) :
    simulate impl (OracleComp.call i x) s = impl i x s := by
  rw [← OracleComp.bind_pure (OracleComp.call i x), OracleComp.call_bind, simulate_query]
  simp only [simulate_pure]
  exact OracleComp.bind_pure _

end Simulate

namespace QueryImpl

/-- A **stateless** implementation: oracle `i` answers query `x` by running `f i x`. -/
def ofComp {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    (f : ∀ i, spec.dom i → OracleComp spec' (spec.rng i)) : QueryImpl spec σ spec' :=
  fun i x s => (f i x).bind (fun y => .pure (y, s))

/-- A stateless implementation runs `f i x` and keeps the state:
`ofComp f i x s = (f i x).bind (fun y => .pure (y, s))`. -/
theorem ofComp_apply {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    (f : ∀ i, spec.dom i → OracleComp spec' (spec.rng i)) (i : ι) (x : spec.dom i) (s : σ) :
    ofComp f i x s = (f i x).bind (fun y => .pure (y, s)) :=
  rfl

/-- **Forwarding:** every query is passed unchanged to the same oracle of the target. -/
def passthrough {spec : OracleSpec ι} : QueryImpl spec σ spec :=
  ofComp (fun i x => OracleComp.call i x)

/-- Forwarding asks the same oracle the same query and keeps the state:
`passthrough i x s = .query i x (fun y => .pure (y, s))`. -/
theorem passthrough_apply {spec : OracleSpec ι} (i : ι) (x : spec.dom i) (s : σ) :
    passthrough (σ := σ) i x s = .query i x (fun y => .pure (y, s)) := by
  rw [passthrough, ofComp_apply, OracleComp.call_bind]

/-- Implement two oracle families **side by side**, sharing one state: `.inl i` is answered by
`impl₁`, and `.inr j` by `impl₂`. -/
def sum {s₁ : OracleSpec ι₁} {s₂ : OracleSpec ι₂} {spec' : OracleSpec ι'}
    (impl₁ : QueryImpl s₁ σ spec') (impl₂ : QueryImpl s₂ σ spec') :
    QueryImpl (s₁.add s₂) σ spec'
  | .inl i => impl₁ i
  | .inr j => impl₂ j

/-- Side by side, the oracle `.inl i` is answered by `impl₁`: `sum impl₁ impl₂ (.inl i) x s =
impl₁ i x s`. -/
theorem sum_inl {s₁ : OracleSpec ι₁} {s₂ : OracleSpec ι₂} {spec' : OracleSpec ι'}
    (impl₁ : QueryImpl s₁ σ spec') (impl₂ : QueryImpl s₂ σ spec') (i : ι₁) (x : s₁.dom i)
    (s : σ) : sum impl₁ impl₂ (.inl i) x s = impl₁ i x s :=
  rfl

/-- Side by side, the oracle `.inr j` is answered by `impl₂`: `sum impl₁ impl₂ (.inr j) x s =
impl₂ j x s`. -/
theorem sum_inr {s₁ : OracleSpec ι₁} {s₂ : OracleSpec ι₂} {spec' : OracleSpec ι'}
    (impl₁ : QueryImpl s₁ σ spec') (impl₂ : QueryImpl s₂ σ spec') (j : ι₂) (x : s₂.dom j)
    (s : σ) : sum impl₁ impl₂ (.inr j) x s = impl₂ j x s :=
  rfl

end QueryImpl

/-! ### Composing implementations -/

/-- **Composition:** answer the queries of `spec` with `impl₁`, whose own queries (to `spec'`)
are answered by `impl₂`; the state is the pair of the two states. This is how a reduction that
answers its adversary's queries by querying its own oracles becomes, after its oracles are
implemented, a single implementation of the adversary's oracles.
[VCVio, SimSemantics/QueryImpl/Compose (QueryImpl.compose)] -/
def QueryImpl.comp {ι'' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    {spec'' : OracleSpec ι''} {σ₁ σ₂ : Type} (impl₂ : QueryImpl spec' σ₂ spec'')
    (impl₁ : QueryImpl spec σ₁ spec') : QueryImpl spec (σ₁ × σ₂) spec'' :=
  fun i x s => (simulate impl₂ (impl₁ i x s.1) s.2).bind (fun p => .pure (p.1.1, (p.1.2, p.2)))

/-- The composed implementation simulates `impl₁`'s answer with `impl₂` and regroups the states:
`impl₂.comp impl₁ i x s =
(simulate impl₂ (impl₁ i x s.1) s.2).bind (fun p => .pure (p.1.1, (p.1.2, p.2)))`. -/
theorem QueryImpl.comp_apply {ι'' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    {spec'' : OracleSpec ι''} {σ₁ σ₂ : Type} (impl₂ : QueryImpl spec' σ₂ spec'')
    (impl₁ : QueryImpl spec σ₁ spec') (i : ι) (x : spec.dom i) (s : σ₁ × σ₂) :
    impl₂.comp impl₁ i x s =
      (simulate impl₂ (impl₁ i x s.1) s.2).bind (fun p => .pure (p.1.1, (p.1.2, p.2))) :=
  rfl

/-- **Simulation composes:** simulating with `impl₂` a simulation by `impl₁` is simulating once
with the composed implementation, up to regrouping the states.
[VCVio, SimSemantics/QueryImpl/Compose (simulateQ_compose)]

**Proof sketch.** Induction on the computation. At a query, both sides first run `impl₁`'s answer
under `impl₂` (`simulate_bind` on the left, the definition of `comp` on the right), and the
continuations agree by induction after associativity. -/
theorem simulate_comp {ι'' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    {spec'' : OracleSpec ι''} {σ₁ σ₂ : Type} (impl₂ : QueryImpl spec' σ₂ spec'')
    (impl₁ : QueryImpl spec σ₁ spec') (c : OracleComp spec α) (s₁ : σ₁) (s₂ : σ₂) :
    simulate impl₂ (simulate impl₁ c s₁) s₂ =
      (simulate (impl₂.comp impl₁) c (s₁, s₂)).bind (fun p => .pure ((p.1, p.2.1), p.2.2)) := by
  induction c generalizing s₁ s₂ with
  | pure a => simp only [simulate_pure, OracleComp.pure_bind]
  | query i x k ih =>
    simp only [simulate_query, simulate_bind, QueryImpl.comp, OracleComp.bind_assoc,
      OracleComp.pure_bind]
    congr 1
    funext p
    exact ih p.1.1 p.1.2 p.2

/-! ### Logging -/

/-- The **log** of a run: the list of its queries, each with the oracle asked, the query and the
answer, in order. [VCVio, QueryTracking/LoggingOracle] -/
abbrev QueryLog {ι : Type} (spec : OracleSpec ι) : Type :=
  List (Σ i, spec.dom i × spec.rng i)

/-- **Logging:** answer as `impl` does, and append each query and its answer to the log kept
beside the state. [VCVio, QueryTracking/LoggingOracle] -/
def QueryImpl.withLog {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    (impl : QueryImpl spec σ spec') : QueryImpl spec (σ × QueryLog spec) spec' :=
  fun i x s => (impl i x s.1).bind (fun ys => .pure (ys.1, (ys.2, s.2 ++ [⟨i, x, ys.1⟩])))

/-- The logged implementation answers as `impl` and appends the entry to the log:
`impl.withLog i x s = (impl i x s.1).bind (fun ys => .pure (ys.1, (ys.2, s.2 ++ [⟨i, x, ys.1⟩])))`.
-/
theorem QueryImpl.withLog_apply {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    (impl : QueryImpl spec σ spec') (i : ι) (x : spec.dom i) (s : σ × QueryLog spec) :
    impl.withLog i x s =
      (impl i x s.1).bind (fun ys => .pure (ys.1, (ys.2, s.2 ++ [⟨i, x, ys.1⟩]))) :=
  rfl

/-- **Logging is conservative:** forgetting the log of a logged simulation gives the plain
simulation, whatever the initial log.

**Proof sketch.** Induction on the computation: at a query, the logged implementation is the
plain one followed by a return that only extends the log, and the continuations agree by
induction. -/
theorem simulate_withLog {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    (impl : QueryImpl spec σ spec') (c : OracleComp spec α) (s : σ) (log : QueryLog spec) :
    (simulate impl.withLog c (s, log)).bind (fun p => .pure (p.1, p.2.1)) =
      simulate impl c s := by
  induction c generalizing s log with
  | pure a => simp only [simulate_pure, OracleComp.pure_bind]
  | query i x k ih =>
    simp only [simulate_query, QueryImpl.withLog, OracleComp.bind_assoc, OracleComp.pure_bind]
    congr 1
    funext ys
    exact ih ys.1 ys.2 _

/-! ### Costs under simulation -/

/-- **Costs under simulation:** if every call to oracle `i` is answered by a computation of cost
at most `b i` (target costs `cost'`), and `c` is cost-bounded by `q` when oracle `i` costs
`b i`, then the simulation of `c` is cost-bounded by `q`. With `b i = 1` for every oracle the
reduction asks once per query, the reduction makes no more target queries than its adversary
makes queries.

**Proof sketch.** Induction on `c`. At a query to oracle `i` with budget `q ≥ b i`, the
implementation fits in `b i`, and the simulated continuation fits in `q - b i` by induction, so
the sequence fits in `b i + (q - b i) = q` (`CostBoundedBy.bind`). -/
theorem simulate_costBoundedBy {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    {impl : QueryImpl spec σ spec'} {cost' : ι' → ℕ} {b : ι → ℕ}
    (himpl : ∀ i x s, OracleComp.CostBoundedBy cost' (impl i x s) (b i))
    {c : OracleComp spec α} {q : ℕ} (hc : OracleComp.CostBoundedBy b c q) (s : σ) :
    OracleComp.CostBoundedBy cost' (simulate impl c s) q := by
  induction c generalizing q s with
  | pure a =>
    rw [simulate_pure]
    exact OracleComp.costBoundedBy_pure cost' (a, s) q
  | query i x k ih =>
    obtain ⟨hi, hk⟩ := (OracleComp.costBoundedBy_query b i x k q).1 hc
    have h := OracleComp.CostBoundedBy.bind (himpl i x s) (fun ys => ih ys.1 (hk ys.1) ys.2)
    rw [Nat.add_sub_cancel' hi] at h
    rw [simulate_query]
    exact h

/-- **A one-shot oracle costs at most one query in total.** Let `good` be an invariant of the
states and `used` mark the states after the costly call. If from a good used state every call is
free and keeps the state good and used, and from a good unused state every call is either free and
keeps the state good and unused, or costs at most `1` and leaves it good and used, then the
simulation of any computation from a good state `s` costs at most `0` (used) or `1` (unused):
`(simulate impl c s).CostBoundedBy cost (if used s then 0 else 1)`.

**Proof sketch.** Induction on the computation; at a query,
`OracleComp.CostBoundedBy.bind_of_allOutputs` with the call's cost and the continuation's
(`0 + 0`, `0 + 1` or `1 + 0`). -/
theorem simulate_costBoundedBy_once {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    (impl : QueryImpl spec σ spec') (cost : ι' → ℕ)
    (good used : σ → Prop) [DecidablePred used]
    (hused : ∀ i x s, good s → used s →
      (impl i x s).CostBoundedBy cost 0 ∧ (impl i x s).AllOutputs fun p => good p.2 ∧ used p.2)
    (hfresh : ∀ i x s, good s → ¬ used s →
      ((impl i x s).CostBoundedBy cost 0 ∧
          (impl i x s).AllOutputs fun p => good p.2 ∧ ¬ used p.2) ∨
        ((impl i x s).CostBoundedBy cost 1 ∧ (impl i x s).AllOutputs fun p => good p.2 ∧ used p.2))
    (c : OracleComp spec α) :
    ∀ s, good s → (simulate impl c s).CostBoundedBy cost (if used s then 0 else 1) := by
  induction c with
  | pure a =>
    intro s _
    rw [simulate_pure]
    exact OracleComp.costBoundedBy_pure _ _ _
  | query i x k ih =>
    intro s hs
    rw [simulate_query]
    by_cases hu : used s
    · obtain ⟨h₀, hP⟩ := hused i x s hs hu
      have := OracleComp.CostBoundedBy.bind_of_allOutputs h₀ hP fun p hp => by
        have h := ih p.1 p.2 hp.1
        rwa [if_pos hp.2] at h
      rwa [if_pos hu]
    · rw [if_neg hu]
      rcases hfresh i x s hs hu with ⟨h₀, hP⟩ | ⟨h₁, hP⟩
      · have := OracleComp.CostBoundedBy.bind_of_allOutputs h₀ hP fun p hp => by
          have h := ih p.1 p.2 hp.1
          rwa [if_neg hp.2] at h
        rwa [Nat.zero_add] at this
      · exact OracleComp.CostBoundedBy.bind_of_allOutputs h₁ hP fun p hp => by
          have h := ih p.1 p.2 hp.1
          rwa [if_pos hp.2] at h

/-! ### Simulation through a state abstraction -/

/-- **Simulation through an abstraction of the state:** if every call of `impl₁` from the
abstract state `f s` is the call of `impl₂` from `s` with its new state abstracted, the same holds
for whole simulations: `simulate impl₁ c (f s) =
(simulate impl₂ c s).bind fun p => pure (p.1, f p.2)`.

**Proof sketch.** Induction on `c`; at a query, rewrite the call by the hypothesis and use the
induction hypothesis on each continuation after associativity. -/
theorem simulate_eq_of_abs {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    {σ₁ σ₂ α : Type} (impl₁ : QueryImpl spec σ₁ spec') (impl₂ : QueryImpl spec σ₂ spec')
    (f : σ₂ → σ₁) (h : ∀ i x s, impl₁ i x (f s) = (impl₂ i x s).bind fun p => .pure (p.1, f p.2))
    (c : OracleComp spec α) (s : σ₂) :
    simulate impl₁ c (f s) = (simulate impl₂ c s).bind fun p => .pure (p.1, f p.2) := by
  induction c generalizing s with
  | pure a => simp only [simulate_pure, OracleComp.pure_bind]
  | query i x k ih =>
    rw [simulate_query, simulate_query, h, OracleComp.bind_assoc, OracleComp.bind_assoc]
    congr 1
    funext p
    rw [OracleComp.pure_bind]
    exact ih p.1 p.2

/-- **Simulation through a state abstraction, along runs with a query budget:** let every call of
`impl₂` from a state `s` with `cnt s < κ` be a deterministic answer `(y, s')` with
`cnt s' ≤ cnt s + 1`, and the call of `impl₁` from `f s` be `(y, f s')`. Then for a computation
`c` with at most `m` queries and `cnt s + m ≤ κ`,
`simulate impl₁ c (f s) = (simulate impl₂ c s).bind fun p => pure (p.1, f p.2)`.

**Proof sketch.** Induction on `c`. A query costs one unit, so it is asked from a state with
`cnt s < κ`; both calls return the same answer, and the continuation runs from `s'` with one unit
less, where `cnt s' + (m - 1) ≤ κ`. -/
theorem simulate_eq_of_abs_bounded {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    {σ₁ σ₂ α : Type} (impl₁ : QueryImpl spec σ₁ spec') (impl₂ : QueryImpl spec σ₂ spec')
    (f : σ₂ → σ₁) (cnt : σ₂ → ℕ) (κ : ℕ)
    (h : ∀ i x s, cnt s < κ → ∃ (y : spec.rng i) (s' : σ₂), impl₂ i x s = .pure (y, s') ∧
      cnt s' ≤ cnt s + 1 ∧ impl₁ i x (f s) = .pure (y, f s'))
    (c : OracleComp spec α) (m : ℕ) (hc : c.CostBoundedBy (fun _ => 1) m) (s : σ₂)
    (hs : cnt s + m ≤ κ) :
    simulate impl₁ c (f s) = (simulate impl₂ c s).bind fun p => .pure (p.1, f p.2) := by
  induction c generalizing m s with
  | pure a => simp only [simulate_pure, OracleComp.pure_bind]
  | query i x k ih =>
    obtain ⟨hm, hk⟩ := (OracleComp.costBoundedBy_query _ _ _ _ _).1 hc
    have hm1 : 1 ≤ m := hm
    obtain ⟨y, s', h₂, hcnt, h₁⟩ := h i x s (by omega)
    rw [simulate_query, simulate_query, h₁, h₂, OracleComp.pure_bind, OracleComp.pure_bind]
    exact ih y (m - 1) (hk y) s' (by omega)

end TCSlib.Cryptography.Games
