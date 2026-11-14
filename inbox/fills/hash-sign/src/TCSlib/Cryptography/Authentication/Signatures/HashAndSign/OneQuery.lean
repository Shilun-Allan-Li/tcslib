/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Machines

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Computations with at most one oracle query

## Main definitions

This module introduces no definitions.

## Main results

* `HashSignFill.eq_pure_of_cost_zero`: a zero-budget computation returns a value.
* `HashSignFill.one_query_cases`: a one-budget computation either returns immediately or
  asks one query and returns a function of its answer.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 144.1 (technical support for its one-query reductions).
-/

namespace TCSlib.Cryptography.Authentication.HashSignFill

open TCSlib.Cryptography.Games

/-- A computation whose every query costs one and whose budget is zero is `pure a` for some
value `a`: a query would require `1 ≤ 0`. -/
theorem eq_pure_of_cost_zero {ι α : Type} {spec : OracleSpec ι}
    (c : OracleComp spec α) (h : c.CostBoundedBy (fun _ => 1) 0) :
    ∃ a, c = .pure a := by
  cases c with
  | pure a => exact ⟨a, rfl⟩
  | query i x k =>
    have hbad := (OracleComp.costBoundedBy_query _ _ _ _ _).mp h
    omega

/-- A computation with unit query costs and budget one either returns immediately or is one
query followed by a return. The continuation of a query has budget zero, so each of its
branches is pure; choosing those return values gives its answer function. -/
theorem one_query_cases {ι α : Type} {spec : OracleSpec ι}
    (c : OracleComp spec α) (h : c.CostBoundedBy (fun _ => 1) 1) :
    (∃ a, c = .pure a) ∨
      ∃ (i : ι) (x : spec.dom i) (f : spec.rng i → α),
        c = .query i x (fun y => .pure (f y)) := by
  classical
  cases c with
  | pure a => exact Or.inl ⟨a, rfl⟩
  | query i x k =>
    have hk := (OracleComp.costBoundedBy_query _ _ _ _ _).mp h
    have hp : ∀ y, ∃ a, k y = .pure a :=
      fun y => eq_pure_of_cost_zero (k y) (hk.2 y)
    choose f hf using hp
    exact Or.inr ⟨i, x, f, congrArg (OracleComp.query i x) (funext hf)⟩

end TCSlib.Cryptography.Authentication.HashSignFill
