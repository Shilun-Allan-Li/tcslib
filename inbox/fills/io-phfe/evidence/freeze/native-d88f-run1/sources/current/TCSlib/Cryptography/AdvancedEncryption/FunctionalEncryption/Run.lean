/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Machines

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Deterministic runs of bounded oracle computations

A reduction can answer an adversary's queries by a deterministic function of its challenge,
fixed advice and current state. The interpreter here follows `Games.buildComp` with precisely
the same query budget, history extension and timeout. It introduces no randomness and builds
no machine.

## Main definitions

* `detImpl`: a deterministic, stateful answer function as an oracle implementation.
* `runDet`: the output and final state of a bounded next-move computation.

## Main results

* `detImpl_apply`: a deterministic implementation returns its answer and next state.
* `runDet_zero_of_ret`, `runDet_zero_of_query`, `runDet_succ_of_ret`,
  `runDet_succ_of_query`: readers for every budget and move constructor.
* `simulate_buildComp_detImpl_eq_pure`: simulation returns the point mass at `runDet`.

## References

* TCSlib contributors, *TCSlib*, `Cryptography/Games/Machines.lean` and
  `Cryptography/Games/Simulate.lean`: the bounded oracle-computation and simulation interfaces.

The declarations here are technical glue for these interfaces, read through their published
case lemmas.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption

open TCSlib.Cryptography.Games

variable {ι ι' α σ : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}

/-- A deterministic answer function is an oracle implementation that returns its answer and
next state with no calls to the target oracles. Technical glue. -/
def detImpl (h : ∀ i, spec.dom i → σ → spec.rng i × σ) : QueryImpl spec σ spec' :=
  fun i x s => .pure (h i x s)

/-- The deterministic implementation answers `i, x` from state `s` by returning `h i x s`:
`detImpl h i x s = pure (h i x s)`. -/
theorem detImpl_apply (h : ∀ i, spec.dom i → σ → spec.rng i × σ)
    (i : ι) (x : spec.dom i) (s : σ) :
    detImpl (spec' := spec') h i x s = .pure (h i x s) := rfl

/-- A bounded next-move computation with deterministic stateful answers returns its output and
final state. A query with no remaining budget returns `timeout` and leaves the state unchanged;
an allowed query appends its query and answer to the history. Technical glue. -/
def runDet (next : QueryLog spec → Move spec α) (timeout : α)
    (h : ∀ i, spec.dom i → σ → spec.rng i × σ) :
    ℕ → QueryLog spec → σ → α × σ
  | 0, hist, s => match next hist with
    | .ret a => (a, s)
    | .query _ _ => (timeout, s)
  | q + 1, hist, s => match next hist with
    | .ret a => (a, s)
    | .query i x =>
      let ys := h i x s
      runDet next timeout h q (hist ++ [⟨i, x, ys.1⟩]) ys.2

section Readers

variable (next : QueryLog spec → Move spec α) (timeout : α)
  (h : ∀ i, spec.dom i → σ → spec.rng i × σ) (hist : QueryLog spec) (s : σ)

/-- With no query budget, a final output `a` is returned with the state unchanged. -/
theorem runDet_zero_of_ret {a : α} (hn : next hist = .ret a) :
    runDet next timeout h 0 hist s = (a, s) := by
  rw [runDet, hn]

/-- With no query budget, a query returns `timeout` with the state unchanged. -/
theorem runDet_zero_of_query {i : ι} {x : spec.dom i} (hn : next hist = .query i x) :
    runDet next timeout h 0 hist s = (timeout, s) := by
  rw [runDet, hn]

/-- With positive query budget, a final output `a` is returned with the state unchanged. -/
theorem runDet_succ_of_ret {q : ℕ} {a : α} (hn : next hist = .ret a) :
    runDet next timeout h (q + 1) hist s = (a, s) := by
  rw [runDet, hn]

/-- With positive query budget, a query consumes one unit, extends the history by its answer,
and continues from the next state supplied by `h`. -/
theorem runDet_succ_of_query {q : ℕ} {i : ι} {x : spec.dom i}
    (hn : next hist = .query i x) :
    runDet next timeout h (q + 1) hist s =
      runDet next timeout h q (hist ++ [⟨i, x, (h i x s).1⟩]) (h i x s).2 := by
  rw [runDet, hn]

end Readers

/-- Simulating a bounded next-move computation with deterministic stateful answers returns the
point mass at its deterministic output and final state. This is the simulation equation used
to relate deterministic reductions to handler realisers. Technical glue.

**Proof sketch.** Induct on the query budget, generalizing the history and state. At budget
zero, the next move either returns or times out; use the corresponding `buildComp` and
`runDet` readers and `simulate_pure`. At positive budget, a return is immediate. For a query,
use `buildComp_succ_of_query`, `simulate_query`, `detImpl_apply` and `OracleComp.pure_bind`;
the induction hypothesis identifies the continuation after the same history extension. -/
theorem simulate_buildComp_detImpl_eq_pure
    (next : QueryLog spec → Move spec α) (timeout : α)
    (h : ∀ i, spec.dom i → σ → spec.rng i × σ)
    (q : ℕ) (hist : QueryLog spec) (s : σ) :
    simulate (detImpl (spec' := spec') h) (buildComp next timeout q hist) s =
      .pure (runDet next timeout h q hist s) := by
  induction q generalizing hist s with
  | zero =>
      -- Budget zero: a return succeeds, while a query times out without a state update.
      cases hn : next hist with
      | ret a =>
          rw [buildComp_zero_of_ret hn, runDet_zero_of_ret next timeout h hist s hn,
            simulate_pure]
      | query i x =>
          rw [buildComp_zero_of_query hn, runDet_zero_of_query next timeout h hist s hn,
            simulate_pure]
  | succ q ih =>
      -- Positive budget: only the query case threads the deterministic answer/state.
      cases hn : next hist with
      | ret a =>
          rw [buildComp_succ_of_ret hn, runDet_succ_of_ret next timeout h hist s hn,
            simulate_pure]
      | query i x =>
          rw [buildComp_succ_of_query hn, runDet_succ_of_query next timeout h hist s hn,
            simulate_query, detImpl_apply, OracleComp.pure_bind]
          exact ih (hist ++ [⟨i, x, (h i x s).1⟩]) (h i x s).2

end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption
