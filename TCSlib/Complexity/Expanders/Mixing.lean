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

## Main results

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
  classical
  -- Coordinate formula for the real inner product.
  have hinner : ∀ x y : EuclideanSpace ℝ (Fin n), inner ℝ x y = ∑ i, x i * y i :=
    fun x y => by
      simp only [PiLp.inner_apply, RCLike.inner_apply, starRingEnd_apply,
        star_trivial]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  -- `A` is self-adjoint: `⟪Ax, y⟫ = ⟪x, Ay⟫`.
  have hself : ∀ x y : EuclideanSpace ℝ (Fin n),
      inner ℝ (toCLM A x) y = inner ℝ x (toCLM A y) := fun x y => by
    rw [hinner, hinner]
    have hx : ∀ i, toCLM A x i = ∑ j, A i j * x j := fun i => rfl
    have hy : ∀ i, toCLM A y i = ∑ j, A i j * y j := fun i => rfl
    simp_rw [hx, hy, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    rw [hA.symm.apply j i]
    ring
  -- Inner products against the uniform vector.
  have hu : ∀ U : Finset (Fin n),
      inner ℝ (indicator U) (uniform n) = (U.card : ℝ) * (n : ℝ)⁻¹ := fun U => by
    rw [hinner]
    show ∑ i, (if i ∈ U then (1 : ℝ) else 0) * (n : ℝ)⁻¹ = _
    rw [← Finset.sum_mul, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
      nsmul_eq_mul, mul_one]
  have huu : inner ℝ (uniform n) (uniform n) = (n : ℝ)⁻¹ := by
    rw [hinner]
    show ∑ _i : Fin n, (n : ℝ)⁻¹ * (n : ℝ)⁻¹ = (n : ℝ)⁻¹
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rcases eq_or_ne (n : ℝ) 0 with h | h
    · rw [h]; simp
    · field_simp
  -- The components of the indicators orthogonal to the uniform direction.
  set sp : EuclideanSpace ℝ (Fin n) :=
    indicator S - (S.card : ℝ) • uniform n with hsp_def
  set tp : EuclideanSpace ℝ (Fin n) :=
    indicator T - (T.card : ℝ) • uniform n with htp_def
  have hsu : inner ℝ sp (uniform n) = 0 := by
    rw [hsp_def, inner_sub_left, real_inner_smul_left, hu, huu, sub_self]
  have htu : inner ℝ tp (uniform n) = 0 := by
    rw [htp_def, inner_sub_left, real_inner_smul_left, hu, huu, sub_self]
  -- The deviation equals `⟪s^⊥, A t^⊥⟫`.
  have hAt : toCLM A (indicator T) = toCLM A tp + (T.card : ℝ) • uniform n := by
    rw [htp_def, map_sub, map_smul, mulVec_uniform hA, sub_add_cancel]
  have h1 : inner ℝ sp ((T.card : ℝ) • uniform n) = 0 := by
    rw [real_inner_smul_right, hsu, mul_zero]
  have h2 : inner ℝ ((S.card : ℝ) • uniform n) (toCLM A tp) = 0 := by
    rw [real_inner_smul_left, ← hself, mulVec_uniform hA, real_inner_comm, htu,
      mul_zero]
  have h3 : inner ℝ ((S.card : ℝ) • uniform n) ((T.card : ℝ) • uniform n) =
      (S.card * T.card : ℝ) / n := by
    rw [real_inner_smul_left, real_inner_smul_right, huu, div_eq_mul_inv]
    ring
  have key : inner ℝ (indicator S) (toCLM A (indicator T)) -
      (S.card * T.card : ℝ) / n = inner ℝ sp (toCLM A tp) := by
    have hs : indicator S = sp + (S.card : ℝ) • uniform n := by
      rw [hsp_def, sub_add_cancel]
    rw [hAt]
    conv_lhs => rw [hs]
    rw [inner_add_left, inner_add_right, inner_add_right, h1, h2, h3]
    ring
  -- Pythagoras: dropping the uniform component shrinks the norm.
  have hperp_le : ∀ x y : EuclideanSpace ℝ (Fin n),
      inner ℝ (x - y) y = 0 → ‖x - y‖ ≤ ‖x‖ := fun x y hxy => by
    have h := norm_add_sq_real (x - y) y
    rw [sub_add_cancel, hxy] at h
    have h2 : ‖x - y‖ ^ 2 ≤ ‖x‖ ^ 2 := by nlinarith [sq_nonneg ‖y‖]
    calc ‖x - y‖ = Real.sqrt (‖x - y‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (‖x‖ ^ 2) := Real.sqrt_le_sqrt h2
      _ = ‖x‖ := Real.sqrt_sq (norm_nonneg _)
  -- The norm of an indicator vector is `√|U|`.
  have hnormInd : ∀ U : Finset (Fin n),
      ‖indicator U‖ = Real.sqrt U.card := fun U => by
    rw [EuclideanSpace.norm_eq]
    congr 1
    have hcoord : ∀ i, ‖indicator U i‖ ^ 2 = if i ∈ U then (1 : ℝ) else 0 :=
      fun i => by
        show ‖(if i ∈ U then (1 : ℝ) else 0)‖ ^ 2 = _
        split <;> simp
    rw [Finset.sum_congr rfl fun i _ => hcoord i, Finset.sum_ite_mem,
      Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hps : ‖sp‖ ≤ Real.sqrt S.card := by
    rw [← hnormInd S]
    refine hperp_le _ _ ?_
    rw [real_inner_smul_right, hsu, mul_zero]
  have hpt : ‖tp‖ ≤ Real.sqrt T.card := by
    rw [← hnormInd T]
    refine hperp_le _ _ ?_
    rw [real_inner_smul_right, htu, mul_zero]
  -- `λ ≥ 0`, so the hypothesis `λ(A) ≤ lam` makes `lam` nonnegative.
  have hlam0 : 0 ≤ lam :=
    le_trans (Real.sSup_nonneg fun x hx => by
      obtain ⟨v, -, rfl⟩ := hx; exact norm_nonneg _) hlam
  -- Put it together with Cauchy–Schwarz and the defining property of `λ`.
  rw [key]
  calc |inner ℝ sp (toCLM A tp)|
      ≤ ‖sp‖ * ‖toCLM A tp‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖sp‖ * (lam * ‖tp‖) := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        exact (norm_mulVec_le_lambda hA htu).trans
          (mul_le_mul_of_nonneg_right hlam (norm_nonneg _))
    _ ≤ Real.sqrt S.card * (lam * Real.sqrt T.card) := by gcongr
    _ = lam * Real.sqrt (S.card * T.card) := by
        rw [Real.sqrt_mul (Nat.cast_nonneg _)]
        ring

end Expander
