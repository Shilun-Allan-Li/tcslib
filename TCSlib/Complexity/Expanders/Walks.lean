/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.Expanders.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.ENNReal.BigOperators

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Expander walks

Random walks driven by a symmetric stochastic matrix, and Arora–Barak's
Theorem 7.38: a random walk on an expander escapes any small vertex set with
probability exponentially close to one.

## Main definitions

* `Expander.unifMatrix` — the matrix `J` with all entries `1/n`.
* `Expander.stepPMF` — one step of the walk from a vertex, as a `PMF`.
* `Expander.walkPMF` — the `k`-step random walk started uniformly, as a `PMF`
  on `Fin (k+1) → Fin n` (a sequence of `k+1` visited vertices).
* `Expander.resMatrix`, `Expander.resVec` — the `B`-restricted transition
  matrix `B̂A` and the vectors `(B̂A)^k B̂𝟙` of the proof of Thm 7.38.

## Main results

* `Expander.opNorm_le_one` — a symmetric stochastic matrix has `L²` operator
  norm at most `1` ([AB09, after Def 7.39], via [AB09, Exercise 10]).
* `Expander.exists_decomposition` — `A = (1−λ)J + λC` with `‖C‖ ≤ 1`
  ([AB09, Lem 7.40]).
* `Expander.walk_filter_sum` — the probability that the walk stays in `B`
  and ends at `j` is the `j`-th entry of `(B̂A)^k B̂𝟙`.
* `Expander.walk_all_mem_le` — the expander-walk bound [AB09, Thm 7.38].

## Deviations from the source

* [AB09, Def 7.39] defines the matrix norm as "the maximum `α` such that
  `‖A𝐯‖₂ ≤ α‖𝐯‖₂` for every `𝐯`" (i.e. the minimum such bound); we use
  Mathlib's `L²` operator norm of the associated continuous linear map, which
  is that quantity.
* [AB09, Thm 7.38] speaks of a `(k−1)`-step walk `X₁,…,X_k` on an
  `(N,d,λ)`-graph and bounds `Pr[∀ i ≤ k, X_i ∈ B] ≤ ((1−λ)√β + λ)^{k−1}`.
  We index by the number of *steps* `k`, so the walk visits `k+1` vertices
  and the bound's exponent is `k`.  As in `Expanders.Basic`, the graph is
  represented by its normalized adjacency matrix, and the eigenvalue bound
  `λ(G) ≤ λ` is a hypothesis `lambda A ≤ lam`; the set-size bound `|B| ≤ βN`
  is the hypothesis `hB`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Expander

open Matrix
open scoped ENNReal

variable {n : ℕ}

/-- The `n × n` matrix `J` with `J i j = 1/n` for every `i, j`: the normalized
adjacency matrix of the `n`-clique with self-loops.  `J𝐩` is the uniform
distribution for every probability vector `𝐩`.  [AB09, Lem 7.40] -/
noncomputable def unifMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun _ _ => (n : ℝ)⁻¹

/-- A symmetric stochastic matrix has `L²` operator norm at most `1`.
[AB09, remark after Def 7.39: "if `A` is a normalized adjacency matrix then
`‖A‖ = 1`"]; the inequality is [AB09, Exercise 10].

**Proof sketch.** For a unit vector `𝐯`, expand `‖A𝐯‖₂²` and apply
Cauchy–Schwarz with the weights `Aᵢⱼ` in each coordinate, using that every
row and every column of `A` sums to one. -/
theorem opNorm_le_one {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsSymmStochastic A) :
    ‖toCLM A‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
    rw [one_mul]
    exact norm_toCLM_apply_le hA v

/-- **Decomposition of an expander step.**  If `A` is symmetric stochastic and
`λ(A) ≤ λ` with `0 ≤ λ`, then `A = (1−λ)J + λC` where `J` is the all-`1/n`
matrix and `‖C‖ ≤ 1`: a step of the walk behaves, for the purposes of `L²`
analysis, like moving to the uniform distribution with probability `1−λ`.
(`C` may have negative entries, so this is not a literal convex combination
of walks.)  [AB09, Lem 7.40], including the degenerate case `λ = 0` the book
permits (e.g. `A = J` itself).

**Proof sketch.** For `λ > 0`, define `C = (1/λ)(A − (1−λ)J)`.  Decompose
any `𝐯` as `𝐮 + 𝐰` with `𝐮 = α𝟙` and `𝐰 ⊥ 𝟙`.  Then `C𝐮 = 𝐮` (both `A` and
`J` fix `𝟙`), and `C𝐰 = (1/λ)A𝐰` (as `J𝐰 = 0`), which has norm at most
`‖𝐰‖₂` by the defining property of `λ`.  Since `C𝐮 = 𝐮 ⊥ C𝐰 ∈ 𝟙^⊥`,
Pythagoras gives `‖C𝐯‖₂ ≤ ‖𝐯‖₂`.  For `λ = 0` the hypothesis forces `A` to
annihilate `𝟙^⊥` (`‖A𝐰‖ ≤ 0`), and `A𝟙 = 𝟙 = J𝟙`, so `A = J`; take
`C = 0`. -/
theorem exists_decomposition {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsSymmStochastic A) {lam : ℝ} (hlam : lambda A ≤ lam)
    (hlam0 : 0 ≤ lam) :
    ∃ C : Matrix (Fin n) (Fin n) ℝ,
      A = (1 - lam) • unifMatrix n + lam • C ∧ ‖toCLM C‖ ≤ 1 := by
  classical
  rcases hlam0.eq_or_lt' with rfl | hpos
  · -- `λ = 0`: the hypothesis forces `A` to annihilate `𝟙^⊥`, so `A = J`.
    refine ⟨0, ?_, ?_⟩
    · have hzero : ∀ w : EuclideanSpace ℝ (Fin n),
          inner ℝ w (uniform n) = 0 → toCLM A w = 0 := fun w hw => by
        have h0 : ‖toCLM A w‖ ≤ 0 :=
          (norm_mulVec_le_lambda hA hw).trans
            (mul_nonpos_of_nonpos_of_nonneg hlam (norm_nonneg _))
        simpa using le_antisymm h0 (norm_nonneg _)
      have hone : ∀ j : Fin n,
          inner ℝ (EuclideanSpace.single j (1 : ℝ)) (uniform n) =
            (n : ℝ)⁻¹ := fun j => by
        rw [inner_eq_sum]
        simp only [EuclideanSpace.single_apply, ite_mul, one_mul, zero_mul,
          Finset.sum_ite_eq', Finset.mem_univ, if_true, uniform_apply]
      have hAe : ∀ j : Fin n,
          toCLM A (EuclideanSpace.single j (1 : ℝ)) = uniform n := fun j => by
        have hw : inner ℝ (EuclideanSpace.single j (1 : ℝ) - uniform n)
            (uniform n) = 0 := by
          rw [inner_sub_left, hone, inner_uniform_self, sub_self]
        have hsplit : toCLM A (EuclideanSpace.single j (1 : ℝ)) =
            toCLM A (EuclideanSpace.single j (1 : ℝ) - uniform n) +
              toCLM A (uniform n) := by
          rw [← map_add, sub_add_cancel]
        rw [hsplit, hzero _ hw, mulVec_uniform hA, zero_add]
      simp only [sub_zero, one_smul, zero_smul, add_zero]
      ext i j
      show A i j = (n : ℝ)⁻¹
      have h2 : toCLM A (EuclideanSpace.single j (1 : ℝ)) i = uniform n i := by
        rw [hAe j]
      rw [toCLM_apply_coord] at h2
      simpa only [EuclideanSpace.single_apply, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true, uniform_apply] using h2
    · have h0 : toCLM (0 : Matrix (Fin n) (Fin n) ℝ) = 0 :=
        map_zero (Matrix.toEuclideanCLM (𝕜 := ℝ))
      rw [h0]
      simp
  · -- `λ > 0`: take `C = (1/λ)(A − (1−λ)J)` and check it contracts.
    refine ⟨lam⁻¹ • (A - (1 - lam) • unifMatrix n), ?_, ?_⟩
    · rw [smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
      abel
    · refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
      rw [one_mul]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · -- `n = 0`: the space is trivial, both norms vanish.
        have hz : ∀ x : EuclideanSpace ℝ (Fin 0), ‖x‖ = 0 := fun x => by
          rw [EuclideanSpace.norm_eq]
          simp
        simp [hz]
      · have hne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
        -- Decompose `v = p + w`, `p` along `𝟙` and `w ⊥ 𝟙`.
        set p : EuclideanSpace ℝ (Fin n) :=
          ((n : ℝ) * inner ℝ v (uniform n)) • uniform n with hp_def
        set w : EuclideanSpace ℝ (Fin n) := v - p with hw_def
        have hvpw : v = p + w := by rw [hw_def, add_comm, sub_add_cancel]
        have hwu : inner ℝ w (uniform n) = 0 := by
          rw [hw_def, hp_def, inner_sub_left, real_inner_smul_left,
            inner_uniform_self, mul_comm ((n : ℝ)) _, mul_assoc,
            mul_inv_cancel₀ hne, mul_one, sub_self]
        have hsumw : (∑ j, w j) = 0 := by
          have h := hwu
          rw [inner_eq_sum] at h
          simp only [uniform_apply] at h
          rw [← Finset.sum_mul] at h
          exact (mul_eq_zero.mp h).resolve_right (inv_ne_zero hne)
        have hJw : toCLM (unifMatrix n) w = 0 := by
          refine PiLp.ext fun i => ?_
          show ∑ j, (n : ℝ)⁻¹ * w j = 0
          rw [← Finset.mul_sum, hsumw, mul_zero]
        have hJu : toCLM (unifMatrix n) (uniform n) = uniform n := by
          refine PiLp.ext fun i => ?_
          show ∑ _j : Fin n, (n : ℝ)⁻¹ * (n : ℝ)⁻¹ = (n : ℝ)⁻¹
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
        have hJp : toCLM (unifMatrix n) p = p := by rw [hp_def, map_smul, hJu]
        have hAp : toCLM A p = p := by
          rw [hp_def, map_smul, mulVec_uniform hA]
        -- `Cv = p + (1/λ)·Aw`.
        have hCv : toCLM (lam⁻¹ • (A - (1 - lam) • unifMatrix n)) v
            = p + lam⁻¹ • toCLM A w := by
          rw [toCLM_smul, toCLM_sub, toCLM_smul]
          simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply]
          rw [hvpw, map_add, map_add, hAp, hJp, hJw, add_zero]
          have hcomb : p + toCLM A w - (1 - lam) • p = lam • p + toCLM A w := by
            rw [sub_smul, one_smul]
            abel
          rw [hcomb, smul_add, smul_smul, inv_mul_cancel₀ hpos.ne', one_smul]
        -- Orthogonality of the two components, before and after `C`.
        have hpw : inner ℝ p w = 0 := by
          rw [hp_def, real_inner_smul_left, real_inner_comm w (uniform n), hwu,
            mul_zero]
        have hpq : inner ℝ p (lam⁻¹ • toCLM A w) = 0 := by
          rw [real_inner_smul_right, hp_def, real_inner_smul_left,
            ← inner_toCLM_right hA.symm, mulVec_uniform hA,
            real_inner_comm w (uniform n), hwu]
          ring
        -- Norm bound on the orthogonal part.
        have hq_le : ‖lam⁻¹ • toCLM A w‖ ≤ ‖w‖ := by
          rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hpos,
            inv_mul_le_iff₀ hpos]
          exact (norm_mulVec_le_lambda hA hwu).trans
            (mul_le_mul_of_nonneg_right hlam (norm_nonneg _))
        -- Pythagoras twice.
        have hv2 : ‖v‖ ^ 2 = ‖p‖ ^ 2 + ‖w‖ ^ 2 := by
          conv_lhs => rw [hvpw]
          rw [norm_add_sq_real, hpw]
          ring
        have hC2 : ‖p + lam⁻¹ • toCLM A w‖ ^ 2 ≤ ‖v‖ ^ 2 := by
          rw [norm_add_sq_real, hpq, hv2]
          nlinarith [hq_le, norm_nonneg (lam⁻¹ • toCLM A w), norm_nonneg w]
        rw [hCv]
        calc ‖p + lam⁻¹ • toCLM A w‖
            = Real.sqrt (‖p + lam⁻¹ • toCLM A w‖ ^ 2) :=
              (Real.sqrt_sq (norm_nonneg _)).symm
          _ ≤ Real.sqrt (‖v‖ ^ 2) := Real.sqrt_le_sqrt hC2
          _ = ‖v‖ := Real.sqrt_sq (norm_nonneg _)

/-- One step of the random walk from vertex `i`: move to `j` with probability
`A i j`.  For the normalized adjacency matrix of a `d`-regular multigraph
this is exactly "choose a random neighbor of `i` (with multiplicity)".
[AB09, §7.A.1] -/
noncomputable def stepPMF {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsSymmStochastic A) (i : Fin n) : PMF (Fin n) :=
  PMF.ofFintype (fun j => ENNReal.ofReal (A i j)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg fun j _ => hA.nonneg i j,
      hA.rowSum i, ENNReal.ofReal_one])

/-- The `B`-restricted transition matrix `B̂A`: row `i` of `A` where `i ∈ B`,
zero rows elsewhere.  One application advances the walk one step and kills
the probability mass outside `B`.  [AB09, proof of Thm 7.38] -/
noncomputable def resMatrix (A : Matrix (Fin n) (Fin n) ℝ) (B : Finset (Fin n)) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => if i ∈ B then A i j else 0

/-- Entrywise formula for the restriction: `resMatrix A B` keeps the rows indexed by `B`
and zeroes the rest, definitionally. -/
@[simp] theorem resMatrix_apply (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Finset (Fin n)) (i j : Fin n) :
    resMatrix A B i j = if i ∈ B then A i j else 0 := rfl

/-- The sub-probability vector of the `B`-restricted walk: `resVec A B k j`
will be shown to equal the probability that the first `k + 1` vertices of the
walk all lie in `B` and the last one is `j` (`Expander.walk_filter_sum`).
[AB09, proof of Thm 7.38: the vector `(B̂A)^k B̂𝟙`] -/
noncomputable def resVec (A : Matrix (Fin n) (Fin n) ℝ) (B : Finset (Fin n)) :
    ℕ → EuclideanSpace ℝ (Fin n)
  | 0 => (WithLp.equiv 2 (Fin n → ℝ)).symm fun j => if j ∈ B then (n : ℝ)⁻¹ else 0
  | k + 1 => toCLM (resMatrix A B) (resVec A B k)

/-- The restricted-walk vectors are entrywise nonnegative. -/
theorem resVec_nonneg {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsSymmStochastic A)
    (B : Finset (Fin n)) : ∀ (k : ℕ) (j : Fin n), 0 ≤ resVec A B k j
  | 0, j => by
    show (0 : ℝ) ≤ if j ∈ B then (n : ℝ)⁻¹ else 0
    split
    · positivity
    · exact le_refl 0
  | k + 1, j => by
    show (0 : ℝ) ≤ ∑ l, (if j ∈ B then A j l else 0) * resVec A B k l
    refine Finset.sum_nonneg fun l _ => mul_nonneg ?_ (resVec_nonneg hA B k l)
    split
    · exact hA.nonneg j l
    · exact le_refl 0

variable [NeZero n]

omit [NeZero n] in
/-- Cauchy–Schwarz against the all-ones vector: the coordinate sum of a
Euclidean vector is at most `√n` times its `L²` norm ([AB09, Note 7.24],
the comparison `|𝐯|₁ ≤ √n·‖𝐯‖₂`, without absolute values on the left). -/
theorem sum_le_sqrt_mul_norm (x : EuclideanSpace ℝ (Fin n)) :
    ∑ j, x j ≤ Real.sqrt n * ‖x‖ := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _ => (1 : ℝ)) (fun j => x j)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] at hcs
  calc ∑ j, x j ≤ |∑ j, x j| := le_abs_self _
    _ = Real.sqrt ((∑ j, x j) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((n : ℝ) * ∑ j, x j ^ 2) := Real.sqrt_le_sqrt hcs
    _ = Real.sqrt n * Real.sqrt (∑ j, x j ^ 2) :=
        Real.sqrt_mul (Nat.cast_nonneg _) _
    _ = Real.sqrt n * ‖x‖ := by
        have hsq : ∑ j, x j ^ 2 = ∑ j, ‖x j‖ ^ 2 :=
          Finset.sum_congr rfl fun j _ => by rw [Real.norm_eq_abs, sq_abs]
        rw [EuclideanSpace.norm_eq, hsq]

/-- The starting vector of the restricted walk has `L²` norm at most
`√β/√n` when `|B| ≤ βn`. -/
theorem norm_resVec_zero_le {A : Matrix (Fin n) (Fin n) ℝ} {B : Finset (Fin n)}
    {β : ℝ} (hβ0 : 0 ≤ β) (hB : (B.card : ℝ) ≤ β * n) :
    ‖resVec A B 0‖ ≤ Real.sqrt β / Real.sqrt n := by
  have hn : (0 : ℝ) < n :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  have hsum : ∑ j, ‖resVec A B 0 j‖ ^ 2 = (B.card : ℝ) * ((n : ℝ)⁻¹) ^ 2 := by
    have hcoord : ∀ j, ‖resVec A B 0 j‖ ^ 2 =
        if j ∈ B then ((n : ℝ)⁻¹) ^ 2 else 0 := fun j => by
      show ‖(if j ∈ B then (n : ℝ)⁻¹ else 0)‖ ^ 2 = _
      split <;> simp
    rw [Finset.sum_congr rfl fun j _ => hcoord j, Finset.sum_ite_mem,
      Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  have hdiv : Real.sqrt β / Real.sqrt n = Real.sqrt (β * (n : ℝ)⁻¹) := by
    rw [Real.sqrt_mul hβ0, Real.sqrt_inv, div_eq_mul_inv]
  rw [EuclideanSpace.norm_eq, hsum, hdiv]
  apply Real.sqrt_le_sqrt
  calc (B.card : ℝ) * ((n : ℝ)⁻¹) ^ 2
      ≤ β * (n : ℝ) * ((n : ℝ)⁻¹) ^ 2 :=
        mul_le_mul_of_nonneg_right hB (by positivity)
    _ = β * ((n : ℝ) * (n : ℝ)⁻¹) * (n : ℝ)⁻¹ := by ring
    _ = β * (n : ℝ)⁻¹ := by rw [mul_inv_cancel₀ hn.ne', mul_one]

/-- The key operator estimate behind [AB09, Thm 7.38]: one `B`-restricted
step shrinks the `L²` norm by a factor `(1−λ)√β + λ`, via the decomposition
`A = (1−λ)J + λC` of [AB09, Lem 7.40]. -/
theorem norm_toCLM_resMatrix_le {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsSymmStochastic A) {lam β : ℝ} (hlam : lambda A ≤ lam)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) {B : Finset (Fin n)}
    (hβ0 : 0 ≤ β) (hB : (B.card : ℝ) ≤ β * n) (x : EuclideanSpace ℝ (Fin n)) :
    ‖toCLM (resMatrix A B) x‖ ≤ ((1 - lam) * Real.sqrt β + lam) * ‖x‖ := by
  classical
  have hn : (0 : ℝ) < n :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  obtain ⟨C, hdecomp, hC⟩ := exists_decomposition hA hlam hlam0
  -- Restriction distributes over the decomposition.
  have hres : resMatrix A B =
      (1 - lam) • resMatrix (unifMatrix n) B + lam • resMatrix C B := by
    ext i j
    have hij : A i j = ((1 - lam) • unifMatrix n + lam • C) i j := by
      rw [← hdecomp]
    by_cases h : i ∈ B <;>
      simp [h, hij, Matrix.add_apply, Matrix.smul_apply, unifMatrix,
        smul_eq_mul]
  -- Restriction never increases the norm of a matrix–vector product.
  have hrestrict : ∀ (M : Matrix (Fin n) (Fin n) ℝ)
      (y : EuclideanSpace ℝ (Fin n)),
      ‖toCLM (resMatrix M B) y‖ ≤ ‖toCLM M y‖ := fun M y => by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    apply Real.sqrt_le_sqrt
    refine Finset.sum_le_sum fun i _ => ?_
    have hcoord : toCLM (resMatrix M B) y i =
        if i ∈ B then toCLM M y i else 0 := by
      rw [toCLM_apply_coord, toCLM_apply_coord]
      by_cases h : i ∈ B
      · rw [if_pos h]
        exact Finset.sum_congr rfl fun j _ => by rw [resMatrix_apply, if_pos h]
      · rw [if_neg h]
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [resMatrix_apply, if_neg h, zero_mul]
    rw [hcoord]
    by_cases h : i ∈ B
    · rw [if_pos h]
    · rw [if_neg h]
      simpa using sq_nonneg ‖toCLM M y i‖
  -- The uniform part: `‖B̂J𝐲‖ ≤ √β‖𝐲‖`.
  have hJ : ∀ y : EuclideanSpace ℝ (Fin n),
      ‖toCLM (resMatrix (unifMatrix n) B) y‖ ≤ Real.sqrt β * ‖y‖ := fun y => by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun _ => (1 : ℝ)) (fun j => y j)
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one] at hcs
    have hcoord : ∀ i, toCLM (resMatrix (unifMatrix n) B) y i =
        if i ∈ B then (n : ℝ)⁻¹ * ∑ j, y j else 0 := fun i => by
      rw [toCLM_apply_coord]
      by_cases h : i ∈ B
      · rw [if_pos h, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [resMatrix_apply, if_pos h]
        rfl
      · rw [if_neg h]
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [resMatrix_apply, if_neg h, zero_mul]
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq,
      show Real.sqrt β * Real.sqrt (∑ j, ‖y j‖ ^ 2) =
        Real.sqrt (β * ∑ j, ‖y j‖ ^ 2) from (Real.sqrt_mul hβ0 _).symm]
    apply Real.sqrt_le_sqrt
    have hsq : ∀ j, ‖y j‖ ^ 2 = y j ^ 2 := fun j => by
      rw [Real.norm_eq_abs, sq_abs]
    calc ∑ i, ‖toCLM (resMatrix (unifMatrix n) B) y i‖ ^ 2
        = ∑ i, (if i ∈ B then ((n : ℝ)⁻¹ * ∑ j, y j) ^ 2 else 0) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hcoord i]
          split
          · rw [Real.norm_eq_abs, sq_abs]
          · simp
      _ = (B.card : ℝ) * ((n : ℝ)⁻¹ * ∑ j, y j) ^ 2 := by
          rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
            nsmul_eq_mul]
      _ ≤ β * (n : ℝ) * ((n : ℝ)⁻¹ * ∑ j, y j) ^ 2 :=
          mul_le_mul_of_nonneg_right hB (sq_nonneg _)
      _ = β * ((n : ℝ) * (n : ℝ)⁻¹) * ((n : ℝ)⁻¹ * (∑ j, y j) ^ 2) := by
          ring
      _ = β * ((n : ℝ)⁻¹ * (∑ j, y j) ^ 2) := by
          rw [mul_inv_cancel₀ hn.ne', mul_one]
      _ ≤ β * ((n : ℝ)⁻¹ * ((n : ℝ) * ∑ j, y j ^ 2)) := by
          refine mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hcs (by positivity)) hβ0
      _ = β * (((n : ℝ)⁻¹ * (n : ℝ)) * ∑ j, y j ^ 2) := by ring
      _ = β * ∑ j, ‖y j‖ ^ 2 := by
          rw [inv_mul_cancel₀ hn.ne', one_mul]
          exact congrArg _ (Finset.sum_congr rfl fun j _ => (hsq j).symm)
  -- Assemble by the triangle inequality.
  have hCb : ∀ y : EuclideanSpace ℝ (Fin n),
      ‖toCLM (resMatrix C B) y‖ ≤ 1 * ‖y‖ := fun y => by
    rw [one_mul]
    refine (hrestrict C y).trans (((toCLM C).le_opNorm y).trans ?_)
    calc ‖toCLM C‖ * ‖y‖
        ≤ 1 * ‖y‖ := mul_le_mul_of_nonneg_right hC (norm_nonneg _)
      _ = ‖y‖ := one_mul _
  calc ‖toCLM (resMatrix A B) x‖
      = ‖(1 - lam) • toCLM (resMatrix (unifMatrix n) B) x +
          lam • toCLM (resMatrix C B) x‖ := by
        rw [hres, toCLM_add, toCLM_smul, toCLM_smul]
        simp only [ContinuousLinearMap.add_apply,
          ContinuousLinearMap.smul_apply]
    _ ≤ ‖(1 - lam) • toCLM (resMatrix (unifMatrix n) B) x‖ +
          ‖lam • toCLM (resMatrix C B) x‖ := norm_add_le _ _
    _ = (1 - lam) * ‖toCLM (resMatrix (unifMatrix n) B) x‖ +
          lam * ‖toCLM (resMatrix C B) x‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - lam), abs_of_nonneg hlam0]
    _ ≤ (1 - lam) * (Real.sqrt β * ‖x‖) + lam * (1 * ‖x‖) := by
        have h1 := hJ x
        have h2 := hCb x
        have h3 : (0:ℝ) ≤ 1 - lam := by linarith
        exact add_le_add (mul_le_mul_of_nonneg_left h1 h3)
          (mul_le_mul_of_nonneg_left h2 hlam0)
    _ = ((1 - lam) * Real.sqrt β + lam) * ‖x‖ := by ring

/-- Iterating the one-step estimate:
`‖(B̂A)^k B̂𝟙‖ ≤ ((1−λ)√β + λ)^k · ‖B̂𝟙‖`. -/
theorem norm_resVec_le {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsSymmStochastic A) {lam β : ℝ} (hlam : lambda A ≤ lam)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) {B : Finset (Fin n)}
    (hβ0 : 0 ≤ β) (hB : (B.card : ℝ) ≤ β * n) (k : ℕ) :
    ‖resVec A B k‖ ≤
      ((1 - lam) * Real.sqrt β + lam) ^ k * ‖resVec A B 0‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hbase0 : 0 ≤ (1 - lam) * Real.sqrt β + lam :=
      add_nonneg (mul_nonneg (by linarith) (Real.sqrt_nonneg _)) hlam0
    calc ‖resVec A B (k + 1)‖
        = ‖toCLM (resMatrix A B) (resVec A B k)‖ := rfl
      _ ≤ ((1 - lam) * Real.sqrt β + lam) * ‖resVec A B k‖ :=
          norm_toCLM_resMatrix_le hA hlam hlam0 hlam1 hβ0 hB _
      _ ≤ ((1 - lam) * Real.sqrt β + lam) *
            (((1 - lam) * Real.sqrt β + lam) ^ k * ‖resVec A B 0‖) :=
          mul_le_mul_of_nonneg_left ih hbase0
      _ = ((1 - lam) * Real.sqrt β + lam) ^ (k + 1) * ‖resVec A B 0‖ := by
          ring

/-- The `k`-step random walk driven by `A`, started at a uniformly random
vertex: a probability distribution on the `k+1` visited vertices
`X₀, X₁, …, X_k` (the book's `X₁, …, X_k` with `k` vertices and `k−1` steps).
[AB09, Thm 7.38] -/
noncomputable def walkPMF {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsSymmStochastic A) : (k : ℕ) → PMF (Fin (k + 1) → Fin n)
  | 0 => (PMF.uniformOfFintype (Fin n)).map fun v _ => v
  | k + 1 => (walkPMF hA k).bind fun f =>
      (stepPMF hA (f (Fin.last k))).map fun j => Fin.snoc f j

/-- The walk of length `0` is the uniform distribution on single vertices:
every one-vertex trajectory has probability `1/n`. -/
theorem walkPMF_zero_apply {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsSymmStochastic A) (f : Fin 1 → Fin n) :
    walkPMF hA 0 f = (n : ℝ≥0∞)⁻¹ := by
  have hf : f = fun _ => f 0 := funext fun i => by rw [Subsingleton.elim i 0]
  show ((PMF.uniformOfFintype (Fin n)).map fun v _ => v) f = _
  rw [PMF.map_apply]
  refine (tsum_eq_single (L := SummationFilter.unconditional _) (f 0)
    fun v hv => ?_).trans ?_
  · exact if_neg fun h => hv (congrFun h 0).symm
  · rw [if_pos hf, PMF.uniformOfFintype_apply, Fintype.card_fin]

/-- Splitting off the last step of a walk: the probability of the trajectory
`g ⌢ j` is the probability of `g` times the transition probability from the
endpoint of `g` to `j`. -/
theorem walkPMF_succ_apply {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsSymmStochastic A) (k : ℕ) (g : Fin (k + 1) → Fin n) (j : Fin n) :
    walkPMF hA (k + 1) (Fin.snoc g j) =
      walkPMF hA k g * ENNReal.ofReal (A (g (Fin.last k)) j) := by
  show ((walkPMF hA k).bind fun f =>
      (stepPMF hA (f (Fin.last k))).map fun j' =>
        (Fin.snoc f j' : Fin (k + 2) → Fin n))
      (Fin.snoc g j) = _
  rw [PMF.bind_apply]
  have hoff : ∀ g' : Fin (k + 1) → Fin n, g' ≠ g →
      walkPMF hA k g' *
        ((stepPMF hA (g' (Fin.last k))).map fun j' =>
          (Fin.snoc g' j' : Fin (k + 2) → Fin n)) (Fin.snoc g j) = 0 :=
      fun g' hg' => by
    have h2 : ((stepPMF hA (g' (Fin.last k))).map fun j' =>
        (Fin.snoc g' j' : Fin (k + 2) → Fin n)) (Fin.snoc g j) = 0 := by
      rw [PMF.map_apply]
      refine ENNReal.tsum_eq_zero.mpr fun j' => if_neg fun h => hg' ?_
      have h3 := congrArg Fin.init h
      rw [Fin.init_snoc, Fin.init_snoc] at h3
      exact h3.symm
    rw [h2, mul_zero]
  rw [tsum_eq_single g hoff]
  congr 1
  rw [PMF.map_apply]
  refine (tsum_eq_single (L := SummationFilter.unconditional _) j
    fun j' hj' => ?_).trans ?_
  · refine if_neg fun h => hj' ?_
    have h2 := congrArg (fun f => f (Fin.last (k + 1))) h
    simp only [Fin.snoc_last] at h2
    exact h2.symm
  · rw [if_pos rfl]
    rfl

/-- The probability that the walk stays inside `B` and ends at `j` is the
`j`-th entry of the restricted-walk vector `resVec A B k`:
in matrix language, of `(B̂A)^k B̂𝟙`.  [AB09, proof of Thm 7.38] -/
theorem walk_filter_sum {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsSymmStochastic A) (B : Finset (Fin n)) :
    ∀ (k : ℕ) (j : Fin n),
      (∑ f ∈ Finset.univ.filter
          (fun f : Fin (k + 1) → Fin n =>
            (∀ i, f i ∈ B) ∧ f (Fin.last k) = j),
        walkPMF hA k f) = ENNReal.ofReal (resVec A B k j)
  | 0, j => by
    classical
    have hn : (0 : ℝ) < n :=
      Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
    by_cases hj : j ∈ B
    · have hfilter : Finset.univ.filter
          (fun f : Fin 1 → Fin n =>
            (∀ i, f i ∈ B) ∧ f (Fin.last 0) = j) = {fun _ => j} := by
        ext f
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_singleton]
        constructor
        · rintro ⟨-, hlast⟩
          exact funext fun i => by rw [Subsingleton.elim i (Fin.last 0), hlast]
        · rintro rfl
          exact ⟨fun _ => hj, rfl⟩
      have hres : resVec A B 0 j = (n : ℝ)⁻¹ := by
        show (if j ∈ B then (n : ℝ)⁻¹ else 0) = _
        rw [if_pos hj]
      rw [hfilter, Finset.sum_singleton, walkPMF_zero_apply hA, hres,
        ENNReal.ofReal_inv_of_pos hn, ENNReal.ofReal_natCast]
    · have hfilter : Finset.univ.filter
          (fun f : Fin 1 → Fin n =>
            (∀ i, f i ∈ B) ∧ f (Fin.last 0) = j) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        exact fun f _ => fun ⟨hall, hlast⟩ => hj (hlast ▸ hall (Fin.last 0))
      have hres : resVec A B 0 j = 0 := by
        show (if j ∈ B then (n : ℝ)⁻¹ else 0) = 0
        rw [if_neg hj]
      rw [hfilter, hres, Finset.sum_empty, ENNReal.ofReal_zero]
  | k + 1, j => by
    classical
    by_cases hj : j ∈ B
    · have hsnoc_mem : ∀ (g : Fin (k + 1) → Fin n) (x : Fin n),
          (∀ i, (Fin.snoc g x : Fin (k + 2) → Fin n) i ∈ B) ↔
            (∀ i, g i ∈ B) ∧ x ∈ B := fun g x => by
        constructor
        · intro h
          refine ⟨fun i => ?_, ?_⟩
          · have h2 := h i.castSucc
            rwa [Fin.snoc_castSucc] at h2
          · have h2 := h (Fin.last _)
            rwa [Fin.snoc_last] at h2
        · rintro ⟨hg, hx⟩ i
          refine Fin.lastCases ?_ (fun i' => ?_) i
          · rwa [Fin.snoc_last]
          · rw [Fin.snoc_castSucc]
            exact hg i'
      rw [Finset.sum_filter,
        ← Fintype.sum_equiv (Fin.snocEquiv fun _ => Fin n)
          (fun p => if (∀ i, (Fin.snoc p.2 p.1 : Fin (k + 2) → Fin n) i ∈ B) ∧
              (Fin.snoc p.2 p.1 : Fin (k + 2) → Fin n) (Fin.last (k + 1)) = j
            then walkPMF hA (k + 1) (Fin.snoc p.2 p.1) else 0)
          (fun f => if (∀ i, f i ∈ B) ∧ f (Fin.last (k + 1)) = j
            then walkPMF hA (k + 1) f else 0)
          (fun p => rfl),
        Fintype.sum_prod_type]
      simp only [Fin.snoc_last, hsnoc_mem, walkPMF_succ_apply hA]
      rw [Finset.sum_eq_single j
        (fun x _ hx => Finset.sum_eq_zero fun g _ => if_neg fun hc => hx hc.2)
        (fun h => absurd (Finset.mem_univ j) h)]
      simp only [hj, and_true]
      rw [← Finset.sum_filter,
        ← Finset.sum_fiberwise
          (Finset.univ.filter fun g : Fin (k + 1) → Fin n => ∀ i, g i ∈ B)
          (fun g => g (Fin.last k))
          (fun g => walkPMF hA k g *
            ENNReal.ofReal (A (g (Fin.last k)) j))]
      have hfiber : ∀ l : Fin n,
          (∑ g ∈ (Finset.univ.filter
              fun g : Fin (k + 1) → Fin n => ∀ i, g i ∈ B).filter
              (fun g => g (Fin.last k) = l),
            walkPMF hA k g * ENNReal.ofReal (A (g (Fin.last k)) j))
            = ENNReal.ofReal (resVec A B k l) *
                ENNReal.ofReal (A l j) := fun l => by
        rw [Finset.filter_filter]
        calc (∑ g ∈ Finset.univ.filter
                (fun g : Fin (k + 1) → Fin n =>
                  (∀ i, g i ∈ B) ∧ g (Fin.last k) = l),
              walkPMF hA k g * ENNReal.ofReal (A (g (Fin.last k)) j))
            = ∑ g ∈ Finset.univ.filter
                (fun g : Fin (k + 1) → Fin n =>
                  (∀ i, g i ∈ B) ∧ g (Fin.last k) = l),
              walkPMF hA k g * ENNReal.ofReal (A l j) :=
              Finset.sum_congr rfl fun g hg => by
                rw [(Finset.mem_filter.mp hg).2.2]
          _ = (∑ g ∈ Finset.univ.filter
                (fun g : Fin (k + 1) → Fin n =>
                  (∀ i, g i ∈ B) ∧ g (Fin.last k) = l),
              walkPMF hA k g) * ENNReal.ofReal (A l j) :=
              (Finset.sum_mul ..).symm
          _ = ENNReal.ofReal (resVec A B k l) * ENNReal.ofReal (A l j) := by
              rw [walk_filter_sum hA B k l]
      rw [Finset.sum_congr rfl fun l _ => hfiber l,
        Finset.sum_congr rfl fun l _ =>
          (ENNReal.ofReal_mul (resVec_nonneg hA B k l)).symm,
        ← ENNReal.ofReal_sum_of_nonneg fun l _ =>
          mul_nonneg (resVec_nonneg hA B k l) (hA.nonneg l j)]
      congr 1
      show ∑ l, resVec A B k l * A l j =
        ∑ l, (if j ∈ B then A j l else 0) * resVec A B k l
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [if_pos hj, hA.symm.apply j l]
      ring
    · have hfilter : Finset.univ.filter
          (fun f : Fin (k + 2) → Fin n =>
            (∀ i, f i ∈ B) ∧ f (Fin.last (k + 1)) = j) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        exact fun f _ => fun ⟨hall, hlast⟩ =>
          hj (hlast ▸ hall (Fin.last (k + 1)))
      have hres : resVec A B (k + 1) j = 0 := by
        show ∑ l, (if j ∈ B then A j l else 0) * resVec A B k l = 0
        refine Finset.sum_eq_zero fun l _ => ?_
        rw [if_neg hj, zero_mul]
      rw [hfilter, hres, Finset.sum_empty, ENNReal.ofReal_zero]

/-- **Expander walks** ([AB09, Thm 7.38]).  Let `A` be symmetric stochastic
with `λ(A) ≤ λ` (for a graph: an `(N,d,λ)`-graph), and let `B` be a set of at
most `βN` vertices.  The probability that a uniformly-started `k`-step random
walk stays inside `B` for all of its `k+1` visited vertices is at most
`((1−λ)√β + λ)^k`.

(The book's statement, with `k` visited vertices, has exponent `k−1`; note
that if `λ, β < 1` are constants then so is `(1−λ)√β + λ`.  The hypothesis
`lam ≤ 1` makes explicit the `λ < 1` of the book's `(N,d,λ)`-graph
[AB09, Def 7.31]; without it the base `(1−λ)√β + λ` can be negative and the
bound false.)

**Proof sketch.** If `β ≥ 1` the bound is trivial: `lam ≤ 1` makes the base
`(1−λ)√β + λ ≥ (1−λ) + λ = 1`, so the right-hand side is at least `1` and
every probability qualifies.  So assume `β < 1`.  With `B̂` the diagonal
projection that zeroes coordinates outside `B`, the probability equals
`|(B̂A)^k B̂𝟙|₁`.  By Lemma 7.40, `B̂A = B̂((1−λ)J + λC)`, so
`‖B̂A‖ ≤ (1−λ)‖B̂J‖ + λ‖B̂C‖ ≤ (1−λ)√β + λ`, since `J`'s image consists of
uniform vectors of which `B̂` keeps `|B| ≤ βN` coordinates, and
`‖B̂‖, ‖C‖ ≤ 1`.  As `‖B̂𝟙‖₂ = √|B|/N ≤ √β/√N` (the hypothesis `hB` is an
inequality, not an equality), we get
`‖(B̂A)^k B̂𝟙‖₂ ≤ ((1−λ)√β + λ)^k √β/√N`, and `|𝐯|₁ ≤ √N ‖𝐯‖₂`
(Note 7.24) concludes, dropping the extra factor `√β`, which is `≤ 1` in
the case `β < 1` under consideration. -/
theorem walk_all_mem_le {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsSymmStochastic A) {lam : ℝ} (hlam : lambda A ≤ lam)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) {B : Finset (Fin n)} {β : ℝ}
    (hβ0 : 0 ≤ β) (hB : (B.card : ℝ) ≤ β * n) (k : ℕ) :
    (walkPMF hA k).toMeasure {f | ∀ i, f i ∈ B} ≤
      ENNReal.ofReal (((1 - lam) * Real.sqrt β + lam) ^ k) := by
  classical
  have hn : (0 : ℝ) < n :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  have hbase0 : 0 ≤ (1 - lam) * Real.sqrt β + lam :=
    add_nonneg (mul_nonneg (by linarith) (Real.sqrt_nonneg _)) hlam0
  rcases le_or_gt 1 β with hβ1 | hβ1
  · -- `β ≥ 1`: the base is at least `1`, so any probability qualifies.
    have hsqrt1 : (1 : ℝ) ≤ Real.sqrt β := by
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt hβ1
    have hb1 : (1 : ℝ) ≤ (1 - lam) * Real.sqrt β + lam := by
      have h := mul_le_mul_of_nonneg_left hsqrt1
        (by linarith : (0 : ℝ) ≤ 1 - lam)
      linarith
    have hbk : (1 : ℝ) ≤ ((1 - lam) * Real.sqrt β + lam) ^ k :=
      one_le_pow₀ hb1
    calc (walkPMF hA k).toMeasure {f | ∀ i, f i ∈ B}
        ≤ 1 := MeasureTheory.prob_le_one
      _ ≤ ENNReal.ofReal (((1 - lam) * Real.sqrt β + lam) ^ k) := by
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal hbk
  · -- `β < 1`: the `L²` estimate via the restricted-walk vectors.
    have hset : {f : Fin (k + 1) → Fin n | ∀ i, f i ∈ B} =
        ↑(Finset.univ.filter fun f : Fin (k + 1) → Fin n =>
          ∀ i, f i ∈ B) := by
      ext f
      simp
    rw [hset, PMF.toMeasure_apply_finset,
      ← Finset.sum_fiberwise
        (Finset.univ.filter fun f : Fin (k + 1) → Fin n => ∀ i, f i ∈ B)
        (fun f => f (Fin.last k)) (fun f => walkPMF hA k f)]
    have hfib : ∀ j : Fin n,
        (∑ f ∈ (Finset.univ.filter
            fun f : Fin (k + 1) → Fin n => ∀ i, f i ∈ B).filter
            (fun f => f (Fin.last k) = j), walkPMF hA k f)
          = ENNReal.ofReal (resVec A B k j) := fun j => by
      rw [Finset.filter_filter]
      exact walk_filter_sum hA B k j
    rw [Finset.sum_congr rfl fun j _ => hfib j,
      ← ENNReal.ofReal_sum_of_nonneg fun j _ => resVec_nonneg hA B k j]
    apply ENNReal.ofReal_le_ofReal
    have hsqrtn : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hn
    have hβle : Real.sqrt β ≤ 1 := by
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt hβ1.le
    calc ∑ j, resVec A B k j
        ≤ Real.sqrt n * ‖resVec A B k‖ := sum_le_sqrt_mul_norm _
      _ ≤ Real.sqrt n *
            (((1 - lam) * Real.sqrt β + lam) ^ k * ‖resVec A B 0‖) :=
          mul_le_mul_of_nonneg_left
            (norm_resVec_le hA hlam hlam0 hlam1 hβ0 hB k) hsqrtn.le
      _ ≤ Real.sqrt n * (((1 - lam) * Real.sqrt β + lam) ^ k *
            (Real.sqrt β / Real.sqrt n)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (norm_resVec_zero_le hβ0 hB)
              (pow_nonneg hbase0 k)) hsqrtn.le
      _ = ((1 - lam) * Real.sqrt β + lam) ^ k * Real.sqrt β := by
          field_simp
      _ ≤ ((1 - lam) * Real.sqrt β + lam) ^ k * 1 :=
          mul_le_mul_of_nonneg_left hβle (pow_nonneg hbase0 k)
      _ = ((1 - lam) * Real.sqrt β + lam) ^ k := mul_one _

end Expander
