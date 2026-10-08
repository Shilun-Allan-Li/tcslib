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

## Main results (sorry-stubbed)

* `Expander.opNorm_le_one` — a symmetric stochastic matrix has `L²` operator
  norm at most `1` ([AB09, after Def 7.39], via [AB09, Exercise 10]).
* `Expander.exists_decomposition` — `A = (1−λ)J + λC` with `‖C‖ ≤ 1`
  ([AB09, Lem 7.40]).
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

variable [NeZero n]

/-- The `k`-step random walk driven by `A`, started at a uniformly random
vertex: a probability distribution on the `k+1` visited vertices
`X₀, X₁, …, X_k` (the book's `X₁, …, X_k` with `k` vertices and `k−1` steps).
[AB09, Thm 7.38] -/
noncomputable def walkPMF {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsSymmStochastic A) : (k : ℕ) → PMF (Fin (k + 1) → Fin n)
  | 0 => (PMF.uniformOfFintype (Fin n)).map fun v _ => v
  | k + 1 => (walkPMF hA k).bind fun f =>
      (stepPMF hA (f (Fin.last k))).map fun j => Fin.snoc f j

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
  sorry

end Expander
