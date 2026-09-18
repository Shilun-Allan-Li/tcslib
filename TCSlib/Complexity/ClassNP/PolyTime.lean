/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Composition

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Polynomial-time computable functions

The function class `FP` underlying every Karp reduction of [AB09, ch. 2]: a function
`f : {0,1}* → {0,1}*` is polynomial-time computable when some machine of this
development computes it within a bound `C · (n + 1)^c`. This module fixes the
polynomial normal form (`Complexity.PolyBound`), the class
(`Complexity.PolyTimeComputable`), and the closure calculus that the chapter's
reductions assemble with — identity, composition, and the output-length bound.

## Design

* **Normal form `C · (n + 1)^c`.** Chapter 1's `P` uses `n^c + 1`; for *function*
  bounds the `(n + 1)^c` shape is closed under the compositions the calculus
  performs and is a monotone majorant by construction (both forms bound the same
  class, by `Complexity.succ_pow_le` and its converse direction). The choice is a
  recorded phase-1 design question.
* **Closure lemmas are need-driven.** Only the combinators the mandatory core
  consumes are stated here; concatenation, constant prefixing, and unary padding
  arrive with the phases that first use them (plan §2), never speculatively.

## Main definitions

* `Complexity.PolyBound` — `p` is bounded by `C · (n + 1)^c`.
* `Complexity.PolyTimeComputable` — `f` is computed by some machine within a
  polynomial bound ([AB09]'s implicit class FP).

## Main results

* `Complexity.polyTimeComputable_id` — the identity is polynomial-time computable.
* `Complexity.PolyTimeComputable.output_length_le` — a polynomial-time computable
  function has polynomially bounded output length.
* `Complexity.PolyTimeComputable.comp` — closure under composition
  [AB09, proof of Theorem 2.8].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§2.2, Definition 2.7 and Theorem 2.8.)
-/

namespace Complexity

open Turing

/-- The bound `p : ℕ → ℕ` is *polynomially bounded*: `p n ≤ C · (n + 1)^c` for some
constants `C, c`. A **numerical helper only**: the *majorant* `C (n+1)^c` is
monotone, but `p` itself need be neither monotone nor computable — which is
exactly why this predicate never appears in a class definition (phase-1 audit,
finding 1: an abstract length function can smuggle undecidable information
through length arithmetic). Class definitions use explicit formulas instead. -/
def PolyBound (p : ℕ → ℕ) : Prop :=
  ∃ C c : ℕ, ∀ n, p n ≤ C * (n + 1) ^ c

/-- A function on binary strings is *polynomial-time computable* when some finite
binary-alphabet machine computes it within `C · (n + 1)^c` steps on inputs of
length `n` — the function class FP implicit throughout [AB09, ch. 2]. -/
def PolyTimeComputable (f : List Bool → List Bool) : Prop :=
  ∃ (M : FinTM Bool) (C c : ℕ), M.ComputesFunInTime f fun n => C * (n + 1) ^ c

/-- The identity function is polynomial-time computable.

**Proof sketch.** `Turing.FinTM.computesFunInTime_id` supplies a machine computing
`id` within a linear bound; enlarge the bound into the `C · (n + 1)^c` normal form
pointwise via `Turing.FinTM.ComputesInTime.mono` (there is no
`ComputesFunInTime`-level monotonicity lemma — phase-1 audit, finding 9). -/
theorem polyTimeComputable_id : PolyTimeComputable id := by
  sorry

/-- A polynomial-time computable function has polynomially bounded output length:
`|f x| ≤ C · (|x| + 1)^c` for some constants `C, c` uniform over all inputs.

**Proof sketch.** A machine emits at most one symbol per step
(`Turing.MultiTapeTM.output_length_le`), so the completed output of a computation
within `t` steps has length at most `t`; instantiate `t` at the machine's own
polynomial budget on each input. -/
theorem PolyTimeComputable.output_length_le {f : List Bool → List Bool}
    (h : PolyTimeComputable f) :
    ∃ C c : ℕ, ∀ x : List Bool, (f x).length ≤ C * (x.length + 1) ^ c := by
  sorry

/-- Polynomial-time computable functions are closed under composition
[AB09, proof of Theorem 2.8: polynomials compose].

**Proof sketch.** Let `Mf` compute `f` within `C · (n + 1)^c` and `Mg` compute `g`
within `C' · (n + 1)^c'`. `Turing.FinTM.computesFunInTime_comp` composes the
machines with a factor-`2` overhead, running `Mg` on the intermediate output
`f x`, whose length is at most `C · (n + 1)^c` because a machine emits at most one
symbol per step (`Turing.MultiTapeTM.output_length_le`). The total budget
`2 · (C (n+1)^c + C' (C (n+1)^c + 1)^{c'} + 1)` is again of the form
`C'' · (n + 1)^{c''}` with `c'' = max c (c · c')` — the `max` covers `c' = 0`,
where the first machine's term still grows as `(n+1)^c` (phase-1 audit,
finding 7); since `(n+1)^c ≥ 1`, the whole budget is absorbed as
`a (C + C'(C+1)^{c'} + 1) (n+1)^{max c (c·c')}`. This is Theorem 2.8's
polynomial-composition observation. -/
theorem PolyTimeComputable.comp {f g : List Bool → List Bool}
    (hg : PolyTimeComputable g) (hf : PolyTimeComputable f) :
    PolyTimeComputable (g ∘ f) := by
  sorry

end Complexity
