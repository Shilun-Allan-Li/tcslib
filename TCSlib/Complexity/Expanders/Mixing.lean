/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.Expanders.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The Expander Mixing Lemma

Arora–Barak's Lemma 7.37: in an `(n,d,λ)`-graph, the number of edges between
any two vertex sets `S` and `T` deviates from its "random-graph" expectation
`(d/n)|S||T|` by at most `λd√(|S||T|)`.

## Main results (sorry-stubbed)

* `Expander.inner_indicator_mulVec_le` — the normalized form
  `|𝐬ᵀA𝐭 − |S||T|/n| ≤ λ√(|S||T|)`, which is [AB09, Lem 7.37, eq. (2)].

## Deviation from the source

[AB09, Lem 7.37] is stated for the edge count `E(S,T)` of an `(n,d,λ)`-graph;
its proof immediately reduces to the equivalent normalized statement (2) about
the normalized adjacency matrix, `|𝐬A𝐭 − |S||T|/n| ≤ λ√(|S||T|)`, which no
longer mentions the degree.  We formalize (2) for an arbitrary symmetric
stochastic matrix with `λ(A) ≤ λ`; the book's form is recovered by
multiplying through by `d`, since `|E(S,T)| = d·𝐬ᵀA(G)𝐭` for the normalized
adjacency matrix of a `d`-regular multigraph (with edges counted with
multiplicity, and, as in the book's convention for `E(S,S̄)`-style counts,
orientation-sensitively).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Expander

open Matrix Finset

variable {n : ℕ}

/-- The indicator vector `𝐬 ∈ ℝⁿ` of a finite set `S` of vertices:
`𝐬ᵢ = 1` if `i ∈ S` and `𝐬ᵢ = 0` otherwise.  [AB09, proof of Lem 7.37] -/
noncomputable def indicator (S : Finset (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  (WithLp.equiv 2 (Fin n → ℝ)).symm fun i => if i ∈ S then 1 else 0

/-- **Expander Mixing Lemma**, normalized form.  For a symmetric stochastic
`A` with `λ(A) ≤ λ` and vertex sets `S, T`,

`|⟨𝐬, A𝐭⟩ − |S||T|/n| ≤ λ·√(|S||T|)`,

where `𝐬, 𝐭` are the indicator vectors of `S, T`.  For the normalized
adjacency matrix of a `d`-regular multigraph, `d·⟨𝐬, A𝐭⟩` is the number of
edges `|E(S,T)|`, so multiplying through by `d` gives the book's statement
`| |E(S,T)| − (d/n)|S||T| | ≤ λd√(|S||T|)`.  [AB09, Lem 7.37, via eq. (2)]

**Proof sketch.** Decompose the indicator vectors against the uniform
direction: `𝐬 = 𝐬∥ + 𝐬⊥` and `𝐭 = 𝐭∥ + 𝐭⊥` with `𝐬∥ = (|S|/n)·n𝟙`,
`𝐭∥ = (|T|/n)·n𝟙` the components along `𝟙` and `𝐬⊥, 𝐭⊥ ⊥ 𝟙`.  Since
`A𝐭∥ = 𝐭∥` and `A𝐭⊥ ⊥ 𝟙` (both from `IsSymmStochastic`),

`⟨𝐬, A𝐭⟩ − |S||T|/n = ⟨𝐬⊥, A𝐭⊥⟩`,

because `⟨𝐬, 𝐭∥⟩ = |S||T|/n` and the cross terms vanish by orthogonality.
Now `|⟨𝐬⊥, A𝐭⊥⟩| ≤ ‖𝐬⊥‖₂·‖A𝐭⊥‖₂ ≤ λ‖𝐬⊥‖₂‖𝐭⊥‖₂ ≤ λ‖𝐬‖₂‖𝐭‖₂ = λ√(|S||T|)`
by Cauchy–Schwarz, the defining property of `λ`
(`Expander.norm_mulVec_le_lambda`), and Pythagoras (`‖𝐬⊥‖ ≤ ‖𝐬‖`).  Both
bounds follow from the single absolute value.  (Deviation from the book's
printed proof: [AB09] argues through the `A = (1−λ)J + λC` decomposition of
Lemma 7.40, which cleanly yields only the upper bound — the lower bound
needs the orthogonal-decomposition argument above, so we use it for
both.) -/
theorem inner_indicator_mulVec_le {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsSymmStochastic A) {lam : ℝ} (hlam : lambda A ≤ lam)
    (S T : Finset (Fin n)) :
    |inner ℝ (indicator S) (toCLM A (indicator T)) -
        (S.card * T.card : ℝ) / n| ≤
      lam * Real.sqrt (S.card * T.card) := by
  sorry

end Expander
