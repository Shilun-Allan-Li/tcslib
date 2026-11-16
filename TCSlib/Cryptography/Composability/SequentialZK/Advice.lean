/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Real.Archimedean

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Finite advice selection with an unbounded witness domain

## Main definitions

This module introduces no definitions.

## Main results

* `exists_uniform_bound_selector` chooses one finite metadata value whose bounds, uniform
  over an arbitrary witness type, imply the same bounds for every metadata value.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 175.1 (sequential repetition of zero knowledge).
-/

namespace TCSlib.Cryptography.Composability

/-- Let `A` be finite and nonempty, let `W` be arbitrary, and suppose
`g a w ≤ M` for every `a : A` and `w : W`, where `0 ≤ M`. There exists `a : A` such that,
for every `ε ≥ 0`, `(∀ w, g a w ≤ ε) → ∀ b w, g b w ≤ ε`.
The selector depends only on `g`, before `ε` is chosen, and need not encode any witness.
[PS10, Theorem 175.1, finite advice selection for the hybrid reduction].

**Proof sketch.** For each metadata value, take the supremum of zero together with all
its witness-indexed values. The sets are nonempty and bounded above by `M`. Select a
metadata value maximizing these finitely many real suprema. A uniform bound at that
selected value bounds its supremum, while each other value is at most its own supremum.
This uses no attainment assumption for the witness-indexed suprema. -/
theorem exists_uniform_bound_selector {A W : Type*} [Finite A] [Nonempty A]
    (g : A → W → ℝ) (M : ℝ) (hM : 0 ≤ M) (hg : ∀ a w, g a w ≤ M) :
    ∃ a : A, ∀ ε : ℝ, 0 ≤ ε →
      (∀ w, g a w ≤ ε) → ∀ b w, g b w ≤ ε := by
  let score (a : A) : ℝ := sSup (insert 0 (Set.range (g a)))
  have hbounded (a : A) : BddAbove (insert 0 (Set.range (g a))) := by
    refine ⟨M, ?_⟩
    intro r hr
    rcases hr with rfl | ⟨w, rfl⟩
    · exact hM
    · exact hg a w
  obtain ⟨a, ha⟩ := Finite.exists_max score
  refine ⟨a, ?_⟩
  intro ε hε hga b w
  have hpoint : g b w ≤ score b :=
    le_csSup (hbounded b) (Or.inr ⟨w, rfl⟩)
  have htop : score a ≤ ε := by
    apply csSup_le (s := insert 0 (Set.range (g a))) ⟨0, Or.inl rfl⟩
    intro r hr
    rcases hr with rfl | ⟨v, rfl⟩
    · exact hε
    · exact hga v
  exact (hpoint.trans (ha b)).trans htop

end TCSlib.Cryptography.Composability
