/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Symmetric

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Symmetric stochastic matrices and the parameter λ

The linear-algebraic foundations of Arora–Barak's appendix 7.A: probability
distributions on vertices as vectors, the normalized adjacency matrix of a
regular graph as a symmetric stochastic matrix, and the parameter `λ(A)` —
the maximum stretch of `A` on the space orthogonal to the uniform
distribution ([AB09, Def 7.25]).

## Main definitions

* `Expander.IsSymmStochastic` — a real square matrix that is symmetric, entrywise
  nonnegative, with every row summing to `1` ([AB09, §7.A.1]).
* `Expander.uniform` — the uniform distribution `(1/n, …, 1/n)` as a vector.
* `Expander.lambda` — the parameter `λ(A)` [AB09, Def 7.25].

## Main results

* `Expander.lambda_nonneg`, `Expander.lambda_le_one` — `0 ≤ λ(A) ≤ 1`
  ([AB09, Rmk 7.26], via Exercise 10).
* `Expander.norm_toCLM_apply_le` — a symmetric stochastic matrix is an `L²`
  contraction ([AB09, Exercise 10]), the helper behind `lambda_le_one` and
  `Expander.opNorm_le_one` in `Expanders.Walks`.
* `Expander.norm_mulVec_le_lambda` — the defining inequality
  `‖A𝐯‖₂ ≤ λ(A)‖𝐯‖₂` for `𝐯 ⊥ 1`.
* `Expander.mulVec_uniform` — `A·1 = 1`: the uniform distribution is stable.

## Deviation from the source

[AB09, §7.A] states these notions for the normalized adjacency matrix of a
`d`-regular `n`-vertex multigraph, remarking that any such matrix is symmetric
stochastic and that the definitions only use that structure.  We take the
symmetric stochastic matrix itself as the primitive object, so every result
applies to a regular multigraph via its normalized adjacency matrix; no graph
type is fixed at this layer.  `λ` is defined by a supremum over the unit
sphere of `1^⊥`, which for `n ≤ 1` is empty; `sSup ∅ = 0` makes `λ = 0` there,
consistent with the convention that a one-vertex graph is a perfect expander.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Expander

open Matrix

variable {n : ℕ}

/-- A real square matrix is *symmetric stochastic* when it is symmetric,
entrywise nonnegative, and every row sums to `1` (hence, by symmetry, every
column does too).  The normalized adjacency matrix `A(G)` of any `d`-regular
multigraph is of this form.  [AB09, §7.A.1] -/
structure IsSymmStochastic (A : Matrix (Fin n) (Fin n) ℝ) : Prop where
  /-- The matrix is symmetric: `Aᵢⱼ = Aⱼᵢ`. -/
  symm : A.IsSymm
  /-- All entries are nonnegative. -/
  nonneg : ∀ i j, 0 ≤ A i j
  /-- Every row sums to one. -/
  rowSum : ∀ i, ∑ j, A i j = 1

/-- The uniform distribution `𝟙 = (1/n, …, 1/n)` on `n` vertices, as a vector
in Euclidean space.  [AB09, Def 7.25] -/
noncomputable def uniform (n : ℕ) : EuclideanSpace ℝ (Fin n) :=
  (WithLp.equiv 2 (Fin n → ℝ)).symm fun _ => (n : ℝ)⁻¹

/-- The action of a matrix on Euclidean space, as a continuous linear map;
`‖·‖` of this map is the `L²` operator norm. -/
noncomputable def toCLM (A : Matrix (Fin n) (Fin n) ℝ) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) A

/-- The parameter `λ(A)`, also written `λ(G)` for the normalized adjacency
matrix of a graph `G`: the maximum of `‖A𝐯‖₂` over all unit vectors `𝐯`
orthogonal to the uniform distribution.  For a symmetric stochastic matrix
this equals the second largest absolute value of an eigenvalue, and `1 - λ(A)`
is the *spectral gap*.  [AB09, Def 7.25] -/
noncomputable def lambda (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sSup ((fun v => ‖toCLM A v‖) ''
    {v : EuclideanSpace ℝ (Fin n) | inner ℝ v (uniform n) = 0 ∧ ‖v‖ = 1})

/-- A symmetric stochastic matrix fixes the uniform distribution: `A𝟙 = 𝟙`.
[AB09, Rmk 7.26: "`A`**1** `=` **1**"]

**Proof sketch.** The `i`-th coordinate of `A𝟙` is `(1/n)·Σⱼ Aᵢⱼ`, and row `i`
sums to one. -/
theorem mulVec_uniform {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsSymmStochastic A) :
    toCLM A (uniform n) = uniform n := by
  refine PiLp.ext fun i => ?_
  show ∑ j, A i j * (n : ℝ)⁻¹ = (n : ℝ)⁻¹
  rw [← Finset.sum_mul, hA.rowSum i, one_mul]

/-- The defining property of `λ`: `A` shrinks any vector orthogonal to the
uniform distribution by a factor of at least `λ(A)`.  [AB09, Def 7.25],
unfolded as used in the proof of [AB09, Lem 7.27].

**Proof sketch.** For `𝐯 = 0` both sides vanish.  Otherwise `𝐯/‖𝐯‖₂` lies in
the unit sphere of `𝟙^⊥`, so `‖A(𝐯/‖𝐯‖₂)‖₂` is one of the values whose
supremum is `λ(A)`; the supremum is attained/bounded because the sphere is
compact and `v ↦ ‖A𝐯‖₂` is continuous.  Multiply through by `‖𝐯‖₂`. -/
theorem norm_mulVec_le_lambda {A : Matrix (Fin n) (Fin n) ℝ}
    (_hA : IsSymmStochastic A) {v : EuclideanSpace ℝ (Fin n)}
    (hv : inner ℝ v (uniform n) = 0) :
    ‖toCLM A v‖ ≤ lambda A * ‖v‖ := by
  rcases eq_or_ne v 0 with rfl | hv0
  · simp
  · have hvn : (0 : ℝ) < ‖v‖ := norm_pos_iff.mpr hv0
    have hbdd : BddAbove ((fun w => ‖toCLM A w‖) ''
        {w : EuclideanSpace ℝ (Fin n) | inner ℝ w (uniform n) = 0 ∧ ‖w‖ = 1}) := by
      refine ⟨‖toCLM A‖, ?_⟩
      rintro x ⟨w, ⟨-, hw1⟩, rfl⟩
      simpa [hw1] using (toCLM A).le_opNorm w
    have hmem : ‖v‖⁻¹ • v ∈
        {w : EuclideanSpace ℝ (Fin n) | inner ℝ w (uniform n) = 0 ∧ ‖w‖ = 1} := by
      refine ⟨?_, ?_⟩
      · rw [real_inner_smul_left, hv, mul_zero]
      · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hvn.ne']
    have hle : ‖toCLM A (‖v‖⁻¹ • v)‖ ≤ lambda A := le_csSup hbdd ⟨_, hmem, rfl⟩
    rw [map_smul, norm_smul, norm_inv, norm_norm] at hle
    calc ‖toCLM A v‖ = ‖v‖ * (‖v‖⁻¹ * ‖toCLM A v‖) := by
          rw [← mul_assoc, mul_inv_cancel₀ hvn.ne', one_mul]
      _ ≤ ‖v‖ * lambda A := mul_le_mul_of_nonneg_left hle hvn.le
      _ = lambda A * ‖v‖ := mul_comm _ _

/-- `λ(A) ≥ 0` (for `n ≥ 2`; for `n ≤ 1` the defining set is empty and
`λ(A) = 0` by convention).  [AB09, Rmk 7.26]

**Proof sketch.** `λ` is a supremum of norms, which are nonnegative; for
`n ≥ 2` the unit sphere of `𝟙^⊥` is nonempty, so the supremum dominates one
such norm. -/
theorem lambda_nonneg (A : Matrix (Fin n) (Fin n) ℝ) (_hn : 2 ≤ n) :
    0 ≤ lambda A :=
  Real.sSup_nonneg fun x hx => by
    obtain ⟨v, -, rfl⟩ := hx
    exact norm_nonneg _

/-- A symmetric stochastic matrix is an `L²` contraction:
`‖A𝐯‖₂ ≤ ‖𝐯‖₂` for every `𝐯`.  This is the pointwise content of
[AB09, Exercise 10] (`‖A‖ ≤ 1`); the bundled operator-norm form is
`Expander.opNorm_le_one` in `Expanders.Walks`.

**Proof.** `(A𝐯)ᵢ² = (Σⱼ Aᵢⱼ𝐯ⱼ)² ≤ (Σⱼ Aᵢⱼ)·(Σⱼ Aᵢⱼ𝐯ⱼ²) = Σⱼ Aᵢⱼ𝐯ⱼ²` by
Cauchy–Schwarz with weights `Aᵢⱼ` (rows sum to one); summing over `i` and
using that columns sum to one (symmetry) gives `Σᵢ(A𝐯)ᵢ² ≤ Σⱼ𝐯ⱼ²`. -/
theorem norm_toCLM_apply_le {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsSymmStochastic A) (v : EuclideanSpace ℝ (Fin n)) :
    ‖toCLM A v‖ ≤ ‖v‖ := by
  have hcol : ∀ j, ∑ i, A i j = 1 := fun j => by
    rw [Finset.sum_congr rfl fun i _ => hA.symm.apply j i]
    exact hA.rowSum j
  have hstep : ∀ i, (∑ j, A i j * v j) ^ 2 ≤ ∑ j, A i j * v j ^ 2 := fun i => by
    have h := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul Finset.univ
      (r := fun j => A i j * v j) (f := fun j => A i j)
      (g := fun j => A i j * v j ^ 2)
      (fun j _ => hA.nonneg i j)
      (fun j _ => mul_nonneg (hA.nonneg i j) (sq_nonneg _))
      (fun j _ => by ring)
    rwa [hA.rowSum i, one_mul] at h
  have hsum : ∑ i, (∑ j, A i j * v j) ^ 2 ≤ ∑ j, v j ^ 2 :=
    calc ∑ i, (∑ j, A i j * v j) ^ 2
        ≤ ∑ i, ∑ j, A i j * v j ^ 2 := Finset.sum_le_sum fun i _ => hstep i
      _ = ∑ j, ∑ i, A i j * v j ^ 2 := Finset.sum_comm
      _ = ∑ j, (∑ i, A i j) * v j ^ 2 :=
          Finset.sum_congr rfl fun j _ => (Finset.sum_mul ..).symm
      _ = ∑ j, v j ^ 2 :=
          Finset.sum_congr rfl fun j _ => by rw [hcol j, one_mul]
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  calc ∑ i, ‖toCLM A v i‖ ^ 2
      = ∑ i, (∑ j, A i j * v j) ^ 2 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Real.norm_eq_abs, sq_abs]
        rfl
    _ ≤ ∑ j, v j ^ 2 := hsum
    _ = ∑ j, ‖v j‖ ^ 2 :=
        Finset.sum_congr rfl fun j _ => by rw [Real.norm_eq_abs, sq_abs]

/-- Every eigenvalue of a symmetric stochastic matrix has absolute value at
most one; consequently `λ(A) ≤ 1`.  [AB09, Rmk 7.26], proved as
[AB09, Exercise 10].

**Proof sketch.** A symmetric stochastic matrix has `L²` operator norm at most
`1`: for any `𝐯`, `(A𝐯)ᵢ² = (Σⱼ Aᵢⱼ𝐯ⱼ)² ≤ Σⱼ Aᵢⱼ𝐯ⱼ²` by Cauchy–Schwarz with
weights `Aᵢⱼ` (rows sum to one), and summing over `i` uses that columns sum to
one (`Expander.norm_toCLM_apply_le`).  The supremum defining `λ` runs over
unit vectors, so it is bounded by the operator norm. -/
theorem lambda_le_one {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsSymmStochastic A) :
    lambda A ≤ 1 := by
  refine Real.sSup_le ?_ zero_le_one
  rintro x ⟨v, ⟨-, hv1⟩, rfl⟩
  exact (norm_toCLM_apply_le hA v).trans_eq hv1

end Expander
