/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.Fintype.Vector
import TCSlib.Complexity.TuringMachine.Finite

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Computable functions

A total string function is *computable* if some finite binary machine computes it,
with no time constraint [AB09, §1.4, p. 20]. This is the notion the uncomputability
results of [AB09, §1.5] refute for `UC` and `HALT`. The machine-level predicate is
`Turing.FinTM.Computes` (in `TCSlib.Complexity.TuringMachine.Finite`); this file
provides the machine-independent class and the bridge back to the time-bounded
notion `Turing.FinTM.ComputesFunInTime`.

## Design and deviations from [AB09]

* Computability is defined for **total** functions `List Bool → List Bool` only, as
  in [AB09]; partial computation is handled at the machine level, by the halting
  relation of a machine (see the two clauses of `Turing.universal`). No time bound,
  and no property of any bound, is part of the definition.
* The name clash with Mathlib's `_root_.Computable` (the `Nat.Partrec`-based notion)
  is deliberate and harmless: ours lives in the `Complexity` namespace, and the
  planned `MathlibBridge` module will relate the two.

## Main definitions

* `Complexity.Computable` — some finite binary machine computes `f`.
  [AB09, §1.4, p. 20]

## Main results

* `Turing.FinTM.Computes.exists_computesFunInTime` — a machine computing `f` with no
  stated time bound admits *some* time bound, by finiteness of the inputs of each
  length. This is the bridge the diagonalization uses to reach the total-function
  normal-form theorems, which are stated with bounds.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.4, p. 20; §1.5.)
-/

namespace Turing.FinTM

/-- A machine computing `f` with no stated time bound admits some time bound: there
are only finitely many inputs of each length, so the maximum halting time over them
is a bound. (Anticipated by the phase-3 audit, round 2, Argument F: "take the finite
maximum of those times at each input length".)

**Proof sketch.** By choice pick, for each input `x`, a halting time `t x`
witnessing `h x`. The inputs of length `n` form a finite type (`List.Vector Symbol
n`, whose `Fintype` instance transports from `Fintype (Fin n → Symbol)`), so
`T n := Finset.univ.sup` of `t` over it is well defined, and
`Turing.FinTM.ComputesInTime.mono` lifts each witness to the bound `T x.length`.
No monotonicity, positivity, or constructibility of `T` is claimed — none is needed
downstream. -/
theorem Computes.exists_computesFunInTime {Symbol : Type} [Fintype Symbol]
    {M : FinTM Symbol} {f : List Symbol → List Symbol} (h : M.Computes f) :
    ∃ T : ℕ → ℕ, M.ComputesFunInTime f T := by
  classical
  choose t ht using h
  let T : ℕ → ℕ := fun n =>
    (Finset.univ : Finset (List.Vector Symbol n)).sup fun x => t x.val
  refine ⟨T, fun x => (ht x).mono ?_⟩
  exact Finset.le_sup (f := fun y : List.Vector Symbol x.length => t y.val)
    (Finset.mem_univ (α := List.Vector Symbol x.length) ⟨x, rfl⟩)

end Turing.FinTM

namespace Complexity

open Turing

/-- A total string function is *computable* if some finite binary machine computes
it — halts on every input with the value on the output tape — with no time
constraint. [AB09, §1.4, p. 20] -/
def Computable (f : List Bool → List Bool) : Prop :=
  ∃ M : FinTM Bool, M.Computes f

end Complexity
