/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty, Mina Sha
-/

import TCSlib.BooleanAnalysis.Hypercontractivity.Applications.KKL.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Elementary influence and junta estimates

## Main definitions

* `noisyTotalInfluence`: degree-weighted noisy Fourier energy.

## Main results

* `KKL_trivial`: the averaging influence bound.
* `friedgut_junta`: a finite-dimensional real-valued junta approximation.
* `balanced_totalInfluence_ge_one`, `influence_entropy_nonneg`.

The finite-dimensional approximation preserves the older API; the exponential
Boolean junta theorem is exported by the parent module.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014, §§1.3–1.4, 2.1–2.4, 3.1, 9.6.
-/

open scoped BigOperators Classical
open BooleanAnalysis

namespace KKL

variable {n : ℕ}

-- Step 13: Noisy influence is monotone in rho (for rho in [0,1]).
-- Inf_i^rho[f] <= Inf_i[f] when 0 <= rho <= 1.
/-- Stable influence at a parameter in `[0,1]` is at most ordinary influence. [OD14, §2.4] -/
lemma noisyInfluence_le_influence (i : Fin n) (f : BooleanFunc n)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    noisyInfluence ρ i f ≤ influence i f := by
  rw [noisyInfluence, influence_eq_sum_fourier]
  apply Finset.sum_le_sum
  intro S _
  split_ifs with hiS
  · exact mul_le_of_le_one_left (sq_nonneg _) (pow_le_one₀ hρ0 hρ1)
  · exact le_refl _

/-- For a Boolean function and `0 < ρ ≤ 1`, stable influence is at most ordinary influence. [OD14, §2.4]
This compatibility lemma states the ordinary influence bound; its name does not assert a fractional-power estimate. -/
lemma noisyInfluence_power_bound (i : Fin n) (f : BooleanFunc n) (_hf : isPmOne f)
    (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) :
    noisyInfluence ρ i f ≤ influence i f := by
  exact noisyInfluence_le_influence i f ρ (le_of_lt hρ0) hρ1

-- Step 15: Sum of squared influences bounded above (Cauchy-Schwarz on influences).
-- (sum_i Inf_i[f])^2 <= n * sum_i (Inf_i[f])^2
/-- The square of total influence is at most the dimension times the sum of squared coordinate influences. Cauchy–Schwarz applied to [OD14, §2.3]. -/
lemma cauchy_schwarz_influences (f : BooleanFunc n) :
    totalInfluence f ^ 2 ≤ n * ∑ i : Fin n, influence i f ^ 2 := by
  have h := @sq_sum_le_card_mul_sum_sq (Fin n) ℝ _ _ _ _ (s := Finset.univ) (f := fun i => influence i f)
  simp only [Finset.card_univ, Fintype.card_fin, totalInfluence] at h ⊢
  exact_mod_cast h

-- Step 16: The max influence is at least (sum_i Inf_i^2) / I[f] (pigeonhole on L2).
-- If I[f] > 0, then max_i Inf_i[f] >= sum_i Inf_i[f]^2 / I[f].
/-- If total influence is positive, some coordinate influence is at least the sum of squared influences divided by total influence. An elementary consequence of [OD14, §2.3].

**Proof sketch.** Choose a coordinate of maximal influence, bound each squared influence by that maximum times its influence, sum and divide. -/
lemma max_influence_from_sum_sq (f : BooleanFunc n) (hI : 0 < totalInfluence f) :
    ∃ i : Fin n, influence i f ≥
      (∑ j : Fin n, influence j f ^ 2) / totalInfluence f := by
  -- n > 0 since I[f] > 0 (if n = 0 the sum is empty, so totalInfluence = 0)
  have hn : 0 < n := by
    by_contra h
    push_neg at h
    interval_cases n
    simp [totalInfluence] at hI
  -- Get the index with maximum influence
  have hne : (Finset.univ : Finset (Fin n)).Nonempty :=
    Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hn)
  obtain ⟨j, _, hj_max⟩ := Finset.exists_max_image Finset.univ (fun i => influence i f) hne
  refine ⟨j, ?_⟩
  rw [ge_iff_le, div_le_iff₀ hI]
  -- Need: ∑ i, Inf_i^2 ≤ influence j f * totalInfluence f
  calc ∑ i : Fin n, influence i f ^ 2
      ≤ ∑ i : Fin n, influence j f * influence i f := by
          apply Finset.sum_le_sum
          intro i _
          rw [sq]
          apply mul_le_mul_of_nonneg_right (hj_max i (Finset.mem_univ i))
          rw [influence_eq_sum_fourier]
          exact Finset.sum_nonneg (fun S _ => by split_ifs <;> positivity)
    _ = influence j f * totalInfluence f := by
          rw [← Finset.mul_sum]; rfl

-- Step 17: KKL Theorem (weak form via Cauchy-Schwarz).
-- This gives max_i Inf_i[f] >= I[f] / n, which is the trivial averaging bound.
-- Already proved in Basic.lean as max_influence_lower_bound.
-- We restate it here for completeness.
/-- In positive dimension, some coordinate influence is at least total influence divided by the dimension. The averaging bound used in [OD14, §9.6]. -/
theorem KKL_trivial (f : BooleanFunc n) (hn : 0 < n) :
    ∃ i : Fin n, influence i f ≥ totalInfluence f / n := by
  exact max_influence_lower_bound f hn

-- Step 19: KKL Theorem (correct statement via hypercontractivity).
-- The proper KKL gives: max_i Inf_i[f] >= Var[f] * c * log(n) / n
-- where Var[f] = E[f^2] - E[f]^2 = sum_S fhat(S)^2 for S nonempty.
-- For balanced (E[f]=0) pm-one functions: Var[f] = 1, so max >= c * log(n)/n.
-- We state a version that follows more directly from hypercontractivity.
-- The Bonami lemma gives: for degree <= k, E[f^4] <= 9^k * (E[f^2])^2.
-- This implies that the "L4 norm" of each level is controlled.

-- Noisy total influence: sum_S |S| * rho^{2|S|} * fhat(S)^2
/-- The degree-weighted Fourier energy after applying noise parameter `ρ` is the sum of `|S|ρ^(2|S|)` times squared coefficients. [OD14, §§2.3–2.4]
This convention uses noisy Fourier energy, rather than stable total influence with weight `ρ^(|S|-1)`. -/
noncomputable def noisyTotalInfluence (ρ : ℝ) (f : BooleanFunc n) : ℝ :=
  ∑ S : Finset (Fin n), S.card * ρ ^ (2 * S.card) * fourierCoeff f S ^ 2

/-! ## Part VI: Friedgut's Junta Theorem -/

-- Step 20: Main Friedgut theorem.
-- For any f with isPmOne and any epsilon > 0,
-- f is epsilon-close in L2 to a junta on at most ceil(2 * I[f] / epsilon) coordinates.

/-- Every Boolean function admits a real-valued junta with squared L² error at most
`ε`, using at most `4n I[f]/ε` coordinates. [OD14, §9.6]
This finite-dimensional approximation is weaker than Friedgut's exponential Boolean
junta theorem: the bound depends on dimension and the approximant is real-valued.

**Proof sketch.** For positive total influence, truncate at degree `ceil(4 I[f]/ε)`
and retain coordinates of influence at least `ε/(4n)`. Each discarded contribution
has squared L² error at most `ε/4`. The squared triangle inequality gives error at
most `ε`; the threshold bounds the coordinate count. Treat zero influence and
zero dimension separately. -/
theorem friedgut_junta (f : BooleanFunc n) (hf : isPmOne f)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (J : Finset (Fin n)) (g : BooleanFunc n),
      (J.card : ℝ) ≤ 4 * n * totalInfluence f / ε ∧
      IsJunta g J ∧
      l2DistSq f g ≤ ε := by
  -- Step A: Choose the degree truncation level
  have hk : 0 < ⌈totalInfluence f / (ε / 2)⌉₊ ∨ totalInfluence f ≤ 0 := by
    by_cases hI : totalInfluence f ≤ 0
    · right; exact hI
    · left
      push_neg at hI
      apply Nat.ceil_pos.mpr
      apply div_pos hI
      linarith
  -- Step B: Low-degree approximation
  have hlow : ∀ (k : ℕ), 0 < k →
      l2DistSq f (lowDegreePart f k) ≤ totalInfluence f / k := by
    intro k hk
    exact lowDegree_approx f k hk
  -- Step C: Junta approximation of lowDegreePart
  -- The lowDegreePart depends on coordinates appearing in its Fourier support.
  -- We approximate it by a junta on influential coordinates.
  have hjunta : ∀ (k : ℕ) (τ : ℝ), 0 < τ →
      ∃ (J : Finset (Fin n)) (g : BooleanFunc n),
        (J.card : ℝ) ≤ totalInfluence f / τ ∧
        IsJunta g J ∧
        l2DistSq (lowDegreePart f k) g ≤ (n : ℝ) * τ := by
    intro k τ hτ
    obtain ⟨g, hg_junta, hg_err⟩ := lowDegreePart_depends_on_influential f k τ hτ
    exact ⟨influentialCoords f τ, g, influential_coords_card f τ hτ, hg_junta, hg_err⟩
  -- Step D: Triangle inequality for L2 and parameter optimization
  -- Triangle inequality: l2DistSq f g ≤ 2*(l2DistSq f h + l2DistSq h g)
  -- (follows from (a-c)^2 ≤ 2*(a-b)^2 + 2*(b-c)^2 pointwise)
  have htri : ∀ (p q r : BooleanFunc n),
      l2DistSq p r ≤ 2 * l2DistSq p q + 2 * l2DistSq q r := by
    intro p q r
    simp only [l2DistSq, expect, uniformWeight]
    have hw : (0 : ℝ) ≤ 2⁻¹ ^ n := by positivity
    calc 2⁻¹ ^ n * ∑ x : BoolCube n, (p x - r x) ^ 2
        ≤ 2⁻¹ ^ n * (2 * ∑ x : BoolCube n, (p x - q x) ^ 2 +
                      2 * ∑ x : BoolCube n, (q x - r x) ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ hw
          have hrw : 2 * ∑ x : BoolCube n, (p x - q x) ^ 2 +
                     2 * ∑ x : BoolCube n, (q x - r x) ^ 2 =
              ∑ x : BoolCube n, (2 * (p x - q x) ^ 2 + 2 * (q x - r x) ^ 2) := by
            simp [Finset.sum_add_distrib, Finset.mul_sum]
          rw [hrw]
          apply Finset.sum_le_sum; intro x _
          nlinarith [sq_nonneg (p x - q x - (q x - r x))]
      _ = 2 * (2⁻¹ ^ n * ∑ x, (p x - q x) ^ 2) +
          2 * (2⁻¹ ^ n * ∑ x, (q x - r x) ^ 2) := by ring
  -- Handle the I[f] = 0 case first
  by_cases hI : totalInfluence f ≤ 0
  · -- I[f] = 0 (since totalInfluence is a sum of nonneg terms)
    have hI0 : totalInfluence f = 0 := le_antisymm hI (by
      rw [totalInfluence_eq_sum_sq_deg]
      apply Finset.sum_nonneg; intro S _; positivity)
    -- Sub-case: n = 0
    by_cases hn : n = 0
    · -- BoolCube 0 is a singleton; f is trivially constant
      refine ⟨∅, f, ?_, ?_, ?_⟩
      · simp [hn]
      · intro x y _
        -- Fin 0 → Bool has a unique element (empty domain)
        subst hn
        exact congrArg f (Subsingleton.elim x y)
      · simp only [l2DistSq]
        have hzero : (fun x : BoolCube n => (f x - f x) ^ 2) = fun _ => (0 : ℝ) := by
          ext x; ring
        rw [hzero]
        simp [expect, uniformWeight, Finset.sum_const_zero]
        linarith
    · -- n > 0, I = 0: use k = 1 and τ = ε/(2*n)
      have hn' : 0 < n := Nat.pos_of_ne_zero hn
      set τ₀ := ε / (2 * (↑n : ℝ)) with hτ₀_def
      have hτ₀ : 0 < τ₀ := by positivity
      have hτ₀n : (↑n : ℝ) * τ₀ = ε / 2 := by
        have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn'
        simp only [hτ₀_def]
        field_simp [hn_pos.ne', hε.ne']
      obtain ⟨J, g, hJcard, hJjunta, hJerr⟩ := hjunta 1 τ₀ hτ₀
      refine ⟨J, g, ?_, hJjunta, ?_⟩
      · -- |J| ≤ I/τ₀ = 0 ≤ 4*n*0/ε
        calc (J.card : ℝ) ≤ totalInfluence f / τ₀ := hJcard
          _ = 0 := by rw [hI0]; simp
          _ ≤ 4 * ↑n * totalInfluence f / ε := by rw [hI0]; simp
      · -- l2DistSq f g ≤ ε
        -- hlow 1: l2DistSq f (lowDeg 1) ≤ I/1 = 0
        -- hJerr: l2DistSq (lowDeg 1) g ≤ n * τ₀ = ε/2
        -- triangle: l2DistSq f g ≤ 2*(0 + ε/2) = ε
        have hlow1 := hlow 1 (by norm_num)
        have hlow_zero : l2DistSq f (lowDegreePart f 1) ≤ 0 := by
          calc l2DistSq f (lowDegreePart f 1) ≤ totalInfluence f / ↑(1 : ℕ) := hlow1
            _ = 0 := by simp [hI0]
        have hjerr_half : l2DistSq (lowDegreePart f 1) g ≤ ε / 2 := by
          calc l2DistSq (lowDegreePart f 1) g ≤ ↑n * τ₀ := hJerr
            _ = ε / 2 := hτ₀n
        have hd_nn : 0 ≤ l2DistSq f (lowDegreePart f 1) := by
          simp only [l2DistSq, expect, uniformWeight]
          apply mul_nonneg (by positivity)
          apply Finset.sum_nonneg; intro x _; positivity
        calc l2DistSq f g
            ≤ 2 * l2DistSq f (lowDegreePart f 1) + 2 * l2DistSq (lowDegreePart f 1) g :=
              htri f (lowDegreePart f 1) g
          _ ≤ 2 * 0 + 2 * (ε / 2) := by linarith
          _ = ε := by ring
  · -- I[f] > 0
    push_neg at hI
    -- Derive n > 0 from I[f] > 0
    have hn : 0 < n := by
      by_contra h0; push_neg at h0
      have h_n0 : n = 0 := Nat.le_zero.mp h0
      subst h_n0
      simp [totalInfluence] at hI
    -- Choose parameters: τ = ε/(4*n), k = ⌈4*I/ε⌉₊
    set τ := ε / (4 * ↑n) with hτ_def
    have hτ : 0 < τ := by positivity
    have hτn : (↑n : ℝ) * τ = ε / 4 := by
      have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn
      simp only [hτ_def]
      field_simp [hn_pos.ne', hε.ne']
    set k := ⌈4 * totalInfluence f / ε⌉₊ with hk_def
    have hk_pos : 0 < k := Nat.ceil_pos.mpr (by positivity)
    -- Get junta from hjunta
    have hlow_k := hlow k hk_pos
    obtain ⟨J, g, hJcard, hJjunta, hJerr⟩ := hjunta k τ hτ
    refine ⟨J, g, ?_, hJjunta, ?_⟩
    -- Junta size bound: |J| ≤ I/τ = 4*n*I/ε
    · calc (J.card : ℝ)
          ≤ totalInfluence f / τ := hJcard
        _ = 4 * ↑n * totalInfluence f / ε := by
            have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn
            simp only [hτ_def]
            field_simp [hn_pos.ne', hε.ne']
    -- L2 error bound: l2DistSq f g ≤ ε
    · -- Low-degree error: I/k ≤ ε/4
      have hlow_bound : l2DistSq f (lowDegreePart f k) ≤ ε / 4 := by
        apply le_trans hlow_k
        rw [div_le_div_iff₀ (Nat.cast_pos.mpr hk_pos) (by norm_num : (0:ℝ) < 4)]
        -- Goal: totalInfluence f * 4 ≤ ε * ↑k
        have hle : 4 * totalInfluence f / ε ≤ (k : ℝ) := Nat.le_ceil _
        have h := (div_le_iff₀ hε).mp hle
        linarith
      -- Junta error: n*τ = ε/4
      have hjunta_bound : l2DistSq (lowDegreePart f k) g ≤ ε / 4 := by
        calc l2DistSq (lowDegreePart f k) g ≤ (↑n) * τ := hJerr
          _ = ε / 4 := hτn
      -- Triangle inequality gives total error ≤ 2*(ε/4 + ε/4) = ε
      calc l2DistSq f g
          ≤ 2 * l2DistSq f (lowDegreePart f k) + 2 * l2DistSq (lowDegreePart f k) g :=
            htri f (lowDegreePart f k) g
        _ ≤ 2 * (ε / 4) + 2 * (ε / 4) := by linarith
        _ = ε := by ring

/-! ## Part VII: Corollaries -/

-- Step 21: For balanced functions, totalInfluence >= 1 (follows from Parseval + KKL setup).
/-- A balanced function taking values in `{-1,1}` has total influence at least one. [OD14, §2.3, Poincaré Inequality] -/
lemma balanced_totalInfluence_ge_one (f : BooleanFunc n) (hf : isPmOne f)
    (hbal : expect f = 0) (_hn : 0 < n) :
    totalInfluence f ≥ 1 := by
  rw [ge_iff_le, ← parseval_pm_one f hf, totalInfluence_eq_sum_sq_deg]
  apply Finset.sum_le_sum
  intro S _
  by_cases hS : S = ∅
  · simp [hS, fourierCoeff_empty, hbal]
  · have hcard : 1 ≤ S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hS)
    have hnn : (0 : ℝ) ≤ fourierCoeff f S ^ 2 := sq_nonneg _
    calc fourierCoeff f S ^ 2
        = 1 * fourierCoeff f S ^ 2 := (one_mul _).symm
      _ ≤ S.card * fourierCoeff f S ^ 2 := by
            apply mul_le_mul_of_nonneg_right _ hnn
            exact_mod_cast hcard

-- Step 22: The influence entropy bound (used in the full KKL proof).
-- sum_i (Inf_i / I[f]) * log(I[f] / Inf_i) >= 0
-- This is just non-negativity of KL divergence / entropy, stated for influences.
/-- For positive total influence, the entropy of normalized coordinate influences is nonnegative, using natural logarithms. An elementary consequence of [OD14, §2.3].

**Proof sketch.** Zero influences contribute zero. For every other coordinate, total influence is at least its influence, so both the normalized weight and the logarithm are nonnegative. Sum these contributions. -/
lemma influence_entropy_nonneg (f : BooleanFunc n) (hI : 0 < totalInfluence f) :
    0 ≤ ∑ i : Fin n,
      (influence i f / totalInfluence f) *
      Real.log (totalInfluence f / influence i f) := by
  apply Finset.sum_nonneg
  intro i _
  have hi_nn : 0 ≤ influence i f := by
    rw [influence_eq_sum_fourier]
    exact Finset.sum_nonneg (fun S _ => by split_ifs <;> positivity)
  by_cases hi : influence i f = 0
  · simp [hi]
  · have hi_pos : 0 < influence i f := lt_of_le_of_ne hi_nn (Ne.symm hi)
    have hle : influence i f ≤ totalInfluence f := by
      show influence i f ≤ ∑ j : Fin n, influence j f
      apply Finset.single_le_sum (f := fun j => influence j f)
        (fun j _ => ?_) (Finset.mem_univ i)
      simp only
      rw [influence_eq_sum_fourier]
      exact Finset.sum_nonneg (fun S _ => by split_ifs <;> positivity)
    apply mul_nonneg
    · exact div_nonneg (le_of_lt hi_pos) (le_of_lt hI)
    · exact Real.log_nonneg ((one_le_div hi_pos).mpr hle)

end KKL
