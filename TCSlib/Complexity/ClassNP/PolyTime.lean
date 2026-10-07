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
  obtain ⟨M, C, hM⟩ := FinTM.computesFunInTime_id
  refine ⟨M, C, 1, fun x => (hM x).mono ?_⟩
  simp only [Nat.pow_one]
  exact Nat.le_refl _

/-- A polynomial-time computable function has polynomially bounded output length:
`|f x| ≤ C · (|x| + 1)^c` for some constants `C, c` uniform over all inputs.

**Proof sketch.** A machine emits at most one symbol per step
(`Turing.MultiTapeTM.output_length_le`), so the completed output of a computation
within `t` steps has length at most `t`; instantiate `t` at the machine's own
polynomial budget on each input. -/
theorem PolyTimeComputable.output_length_le {f : List Bool → List Bool}
    (h : PolyTimeComputable f) :
    ∃ C c : ℕ, ∀ x : List Bool, (f x).length ≤ C * (x.length + 1) ^ c := by
  obtain ⟨M, C, c, hM⟩ := h
  refine ⟨C, c, fun x => ?_⟩
  have hout := ((FinTM.computesInTime_iff _ _ _ _).mp (hM x)).2
  simpa only [hout] using M.tm.output_length_le x (C * (x.length + 1) ^ c)

/-- The timed-composition budget is bounded by a polynomial of degree
`max c (c * c')`, uniformly in all natural coefficients, degrees, and lengths.

**Proof sketch.** Since `(n+1)^c ≥ 1`, the inner argument is at most
`(C+1)(n+1)^c`. Raising to `c'` gives the second term degree `c*c'`.
Enlarge both degrees to their maximum, absorb the constant term using
`(n+1)^(max c (c*c')) ≥ 1`, and distribute the common power. -/
private lemma comp_time_bound (a C c C' c' n : ℕ) :
    a * (C * (n + 1) ^ c + C' * (C * (n + 1) ^ c + 1) ^ c' + 1) ≤
      a * (C + C' * (C + 1) ^ c' + 1) * (n + 1) ^ max c (c * c') := by
  have hpos : 0 < n + 1 := Nat.succ_pos n
  have hone : 1 ≤ (n + 1) ^ c := Nat.one_le_pow c (n + 1) hpos
  have hfirst : (n + 1) ^ c ≤ (n + 1) ^ max c (c * c') :=
    Nat.pow_le_pow_right hpos (Nat.le_max_left _ _)
  have hsecond : (C * (n + 1) ^ c + 1) ^ c' ≤
      (C + 1) ^ c' * (n + 1) ^ max c (c * c') := by
    calc
      (C * (n + 1) ^ c + 1) ^ c' ≤ ((C + 1) * (n + 1) ^ c) ^ c' :=
        Nat.pow_le_pow_left (by
          rw [Nat.add_mul, Nat.one_mul]
          exact Nat.add_le_add_left hone _) c'
      _ = (C + 1) ^ c' * (n + 1) ^ (c * c') := by
        rw [Nat.mul_pow, ← Nat.pow_mul]
      _ ≤ (C + 1) ^ c' * (n + 1) ^ max c (c * c') :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hpos (Nat.le_max_right _ _))
  calc
    a * (C * (n + 1) ^ c + C' * (C * (n + 1) ^ c + 1) ^ c' + 1) ≤
        a * (C * (n + 1) ^ max c (c * c') +
          C' * ((C + 1) ^ c' * (n + 1) ^ max c (c * c')) +
          (n + 1) ^ max c (c * c')) :=
      Nat.mul_le_mul_left a (Nat.add_le_add
        (Nat.add_le_add (Nat.mul_le_mul_left C hfirst) (Nat.mul_le_mul_left C' hsecond))
        (Nat.one_le_pow _ _ hpos))
    _ = a * (C + C' * (C + 1) ^ c' + 1) * (n + 1) ^ max c (c * c') := by
      simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.one_mul]

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
  obtain ⟨Mf, C, c, hf⟩ := hf
  obtain ⟨Mg, C', c', hg⟩ := hg
  have hmono : Monotone (fun n : ℕ => C' * (n + 1) ^ c') := by
    intro m n hmn
    exact Nat.mul_le_mul_left C' (Nat.pow_le_pow_left (Nat.add_le_add_right hmn 1) c')
  obtain ⟨M, a, hM⟩ := FinTM.computesFunInTime_comp hf hg hmono
  refine ⟨M, a * (C + C' * (C + 1) ^ c' + 1), max c (c * c'),
    fun x => (hM x).mono ?_⟩
  exact comp_time_bound a C c C' c' x.length

end Complexity
