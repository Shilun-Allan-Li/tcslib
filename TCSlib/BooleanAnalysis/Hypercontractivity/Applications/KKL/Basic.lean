/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty, Mina Sha
-/

import TCSlib.BooleanAnalysis.Basic
import TCSlib.BooleanAnalysis.ThresholdFunctions.Polynomial
import TCSlib.BooleanAnalysis.Hypercontractivity.Cube.Bonami
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Nat.Choose.Bounds

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Fourier definitions and approximation for KKL

## Main definitions

* `noisyInfluence`, `lowDegreePart`, `highDegreePart`.
* `influentialCoords`, `IsJunta`, `l2DistSq`.

## Main results

* `fourierCoeff_highDegreePart`: the coefficient formula above a cutoff.
* `influence_lowDegreePart_le`: truncation cannot increase influence.
* `influence_noiseOp_le_noisyInfluence`: noise converts noisy influence to an ordinary bound.
* `lowDegree_approx`: the influence bound for the Fourier tail.
* `influential_coords_card`: the number of coordinates above a threshold.
* `card_bounded_subsets_le`: a polynomial count of subsets below a degree cutoff.
* `lowDegreePart_depends_on_influential`: a finite-dimensional junta approximation.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014, §§1.3–1.4, 2.1–2.4, 3.1, 9.6.
-/

open scoped BigOperators Classical
open BooleanAnalysis

namespace KKL

variable {n : ℕ}

/-! ## Part I: Definitions -/

/-- The noisy influence of coordinate `i` at noise rate `rho`:
    `Inf_i^rho[f] = sum_{S ni i} rho^{|S|-1} * fhat(S)^2`.

**Source:** [OD14, §2.4]. -/
noncomputable def noisyInfluence (ρ : ℝ) (i : Fin n) (f : BooleanFunc n) : ℝ :=
  ∑ S : Finset (Fin n),
    if i ∈ S then ρ ^ (S.card - 1) * fourierCoeff f S ^ 2 else 0

/-- The low-degree truncation of `f`: keep Fourier coefficients at levels `<= k`.
    `f_{<=k}(x) = sum_{|S| <= k} fhat(S) * chi_S(x)`.

**Source:** [OD14, §3.1]. -/
noncomputable def lowDegreePart (f : BooleanFunc n) (k : ℕ) : BooleanFunc n :=
  fun x => ∑ S : Finset (Fin n),
    if S.card ≤ k then fourierCoeff f S * chiS S x else 0

/-- The high-degree part of `f`: Fourier coefficients at levels `> k`.
    `f_{>k}(x) = sum_{|S| > k} fhat(S) * chi_S(x)`.

**Source:** [OD14, §3.1]. -/
noncomputable def highDegreePart (f : BooleanFunc n) (k : ℕ) : BooleanFunc n :=
  fun x => ∑ S : Finset (Fin n),
    if k < S.card then fourierCoeff f S * chiS S x else 0

/-- The set of `tau`-influential coordinates:
    `J_tau(f) = {i : Fin n | Inf_i[f] >= tau}`.

**Source:** [OD14, Thm. 9.28]. -/
noncomputable def influentialCoords (f : BooleanFunc n) (τ : ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => τ ≤ influence i f)

/-- Defines a `J`-junta as a function depending only on coordinates in `J`.

This predicate is extended to real-valued functions.

**Source:** [OD14, §2.1]. -/
def IsJunta (g : BooleanFunc n) (J : Finset (Fin n)) : Prop :=
  ∀ x y : BoolCube n, (∀ i ∈ J, x i = y i) → g x = g y

/-- Defines the squared `L²` distance between two Boolean functions.

**Source:** [OD14, §1.4]. -/
noncomputable def l2DistSq (f g : BooleanFunc n) : ℝ :=
  expect (fun x => (f x - g x) ^ 2)

/-! ## Part II: Basic Fourier lemmas for KKL -/

-- Step 01: The noisy influence at rho = 1 equals the standard influence.
/-- Stable influence at parameter one equals ordinary influence. [OD14, §2.4] -/
lemma noisyInfluence_one (i : Fin n) (f : BooleanFunc n) :
    noisyInfluence 1 i f = influence i f := by
  rw [noisyInfluence, influence_eq_sum_fourier]
  congr 1; ext S
  split_ifs <;> simp

-- Step 02: Sum of noisy influences equals the "noisy total influence".
/-- Summing stable influences over coordinates gives the degree-weighted Fourier sum with weight `ρ^(|S|-1)`. [OD14, §2.4] -/
lemma sum_noisyInfluence (ρ : ℝ) (f : BooleanFunc n) :
    ∑ i : Fin n, noisyInfluence ρ i f =
    ∑ S : Finset (Fin n), S.card * ρ ^ (S.card - 1) * fourierCoeff f S ^ 2 := by
  simp only [noisyInfluence]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [Finset.sum_const, nsmul_eq_mul]
  ring

-- Step 03: The total influence is the sum of influences (definitional unfolding).
/-- Total influence is the sum of the coordinate influences. [OD14, §2.3] -/
lemma totalInfluence_eq_sum_influences (f : BooleanFunc n) :
    totalInfluence f = ∑ i : Fin n, influence i f := by
  rfl

-- Step 04: For isPmOne functions, expect(f^2) = 1.
/-- The mean square of a function taking values in `{-1,1}` is one. [OD14, §1.4] -/
lemma expect_sq_pm_one (f : BooleanFunc n) (hf : isPmOne f) :
    expect (fun x => f x ^ 2) = 1 := by
  have h := innerProduct_self_pm_one f hf
  simp only [innerProduct] at h
  convert h using 1
  congr 1
  ext x
  ring

-- Step 05: Parseval identity restated: sum of fhat(S)^2 = expect(f^2).
/-- Parseval's identity identifies total squared Fourier weight with mean square. [OD14, §1.4] -/
lemma sum_fourier_sq_eq_expect_sq (f : BooleanFunc n) :
    ∑ S : Finset (Fin n), fourierCoeff f S ^ 2 = expect (fun x => f x ^ 2) := by
  rw [← parseval, innerProduct]
  congr 1; ext x; ring

/-! ## Part III: Low-degree approximation (for Friedgut) -/

-- Step 06: f = lowDegreePart f k + highDegreePart f k (pointwise).
/-- The degree-at-most-`k` and degree-above-`k` Fourier parts sum pointwise to the original function. [OD14, §3.1] -/
lemma low_plus_high_eq (f : BooleanFunc n) (k : ℕ) (x : BoolCube n) :
    lowDegreePart f k x + highDegreePart f k x = f x := by
  simp only [lowDegreePart, highDegreePart]
  rw [← Finset.sum_add_distrib]
  have : ∀ S ∈ (Finset.univ : Finset (Finset (Fin n))),
      (if S.card ≤ k then fourierCoeff f S * chiS S x else 0) +
      (if k < S.card then fourierCoeff f S * chiS S x else 0) =
      fourierCoeff f S * chiS S x := by
    intro S _
    by_cases h : S.card ≤ k
    · simp [h, Nat.not_lt.mpr h]
    · simp [h, Nat.lt_of_not_le h]
  rw [Finset.sum_congr rfl this]
  exact (walsh_expansion f x).symm

-- Step 07: The Fourier coefficient of lowDegreePart is the truncated coefficient.
/-- Degree truncation preserves Fourier coefficients at levels at most `k` and sets the remaining coefficients to zero. [OD14, §§1.3–1.4, 3.1]

**Proof sketch.** Expand the truncation in parity characters, exchange the finite sums, and use orthonormality to retain only the requested character. -/
lemma fourierCoeff_lowDegreePart (f : BooleanFunc n) (k : ℕ) (S : Finset (Fin n)) :
    fourierCoeff (lowDegreePart f k) S =
    if S.card ≤ k then fourierCoeff f S else 0 := by
  -- Step 1: Express fourierCoeff of lowDegreePart using linearity
  -- fourierCoeff (lowDegreePart f k) S = innerProduct (lowDegreePart f k) (chiS S)
  -- = expect (fun x => (∑ T, if |T|≤k then fhat(T)*χ_T(x) else 0) * χ_S(x))
  -- = ∑ T, if |T|≤k then fhat(T) * expect (χ_T * χ_S) else 0
  -- = ∑ T, if |T|≤k then fhat(T) * innerProduct χ_T χ_S else 0
  -- = ∑ T, if |T|≤k then fhat(T) * (if T=S then 1 else 0) else 0
  -- = if |S|≤k then fhat(S) else 0
  show fourierCoeff (lowDegreePart f k) S = if S.card ≤ k then fourierCoeff f S else 0
  unfold lowDegreePart
  unfold BooleanAnalysis.fourierCoeff innerProduct expect
  beta_reduce
  -- After unfolding: LHS = uniformWeight n * ∑ x, (∑ T, if T.card ≤ k then fhat_unfolded(T) * χ_T(x) else 0) * χ_S(x)
  -- where fhat_unfolded(T) = uniformWeight n * ∑ y, f y * χ_T y
  -- RHS = if S.card ≤ k then uniformWeight n * ∑ x, f x * χ_S x else 0
  -- We will abbreviate fhat T := uniformWeight n * ∑ y, f y * χ_T y
  set w := uniformWeight n
  set fhat : Finset (Fin n) → ℝ := fun T => w * ∑ y, f y * chiS T y
  -- Now rearrange the LHS
  have step1 : w * ∑ x, (∑ T : Finset (Fin n), if T.card ≤ k then fhat T * chiS T x else 0) * chiS S x =
      ∑ T : Finset (Fin n), if T.card ≤ k then fhat T * (w * ∑ x, chiS T x * chiS S x) else 0 := by
    rw [Finset.mul_sum]
    conv_lhs => arg 2; ext x; rw [Finset.sum_mul]
    simp_rw [show ∀ (T : Finset (Fin n)) (x : BoolCube n),
        (if T.card ≤ k then fhat T * chiS T x else 0) * chiS S x =
        (if T.card ≤ k then fhat T * (chiS T x * chiS S x) else 0) from by
      intros; split_ifs <;> ring]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    congr 1; ext T
    split_ifs with hT
    · congr 1; ext x; ring
    · simp
  rw [step1]
  -- Now w * ∑ x, chiS T x * chiS S x = innerProduct (chiS T) (chiS S) (after folding)
  -- But everything is unfolded, so we use fourier_coeff_chi directly
  have ortho : ∀ T : Finset (Fin n),
      w * ∑ x, chiS T x * chiS S x = if T = S then 1 else 0 := by
    intro T
    have := fourier_coeff_chi T S
    simp only [innerProduct, expect] at this
    exact this
  simp_rw [ortho]
  -- Now: ∑ T, if T.card ≤ k then fhat T * (if T = S then 1 else 0) else 0
  --    = if S.card ≤ k then fhat S else 0
  simp only [mul_ite, mul_one, mul_zero]
  -- Goal: ∑ T, if T.card ≤ k then (if T = S then fhat T else 0) else 0
  --     = if S.card ≤ k then w * ∑ x, f x * chiS S x else 0
  -- Collapse nested ifs
  conv_lhs => arg 2; ext T; rw [show (if T.card ≤ k then (if T = S then fhat T else 0) else 0) =
    (if T = S then (if S.card ≤ k then fhat S else 0) else 0) from by
    split_ifs <;> simp_all]
  simp [Finset.sum_ite_eq', fhat]

/-- The high-degree part retains exactly the Fourier coefficients strictly
above the cutoff. [OD14, §§1.4, 3.1] -/
lemma fourierCoeff_highDegreePart (f : BooleanFunc n) (d : ℕ) (T : Finset (Fin n)) :
    fourierCoeff (highDegreePart f d) T =
      if d < T.card then fourierCoeff f T else 0 := by
  classical
  have he : highDegreePart f d = ThresholdFunctions.MultilinearPolynomial.eval
      (fun S => if d < S.card then fourierCoeff f S else 0) := by
    funext x
    simp only [highDegreePart, ThresholdFunctions.MultilinearPolynomial.eval, ite_mul, zero_mul]
  rw [he]
  exact ThresholdFunctions.MultilinearPolynomial.fourierCoeff_eval _ T

/-- Removing Fourier levels above a cutoff cannot increase any influence.
[OD14, §3.1, Fourier influence formula] -/
lemma influence_lowDegreePart_le (f : BooleanFunc n) (d : ℕ) (i : Fin n) :
    influence i (lowDegreePart f d) ≤ influence i f := by
  classical
  rw [influence_eq_sum_fourier, influence_eq_sum_fourier]
  apply Finset.sum_le_sum
  intro S hS
  by_cases hi : i ∈ S
  · simp only [if_pos hi, fourierCoeff_lowDegreePart]
    split_ifs <;> simp [sq_nonneg]
  · simp only [if_neg hi, le_refl]

/-- Ordinary influence after noise smoothing is bounded by the noisy influence
of the original function at the same radius. [OD14, Cor. 11.69 (proof)] -/
lemma influence_noiseOp_le_noisyInfluence (f : BooleanFunc n) (i : Fin n)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    influence i (noiseOp ρ f) ≤ noisyInfluence ρ i f := by
  classical
  rw [influence_eq_sum_fourier, noisyInfluence]
  apply Finset.sum_le_sum
  intro S hS
  by_cases hi : i ∈ S
  · simp only [if_pos hi, noiseOp_fourier, mul_pow]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    rw [← pow_mul]
    exact pow_le_pow_of_le_one hρ0 hρ1 (by omega)
  · simp only [if_neg hi, le_refl]

-- Step 08: The L2 error of low-degree truncation is the tail Fourier weight.
/-- The squared L² error of degree truncation is exactly the Fourier weight above the cutoff. [OD14, §§1.4, 3.1]

**Proof sketch.** The difference is the high-degree part. Apply Parseval and coefficient truncation to retain precisely the terms above the cutoff. -/
lemma lowDegree_l2_error (f : BooleanFunc n) (k : ℕ) :
    l2DistSq f (lowDegreePart f k) =
    ∑ S : Finset (Fin n), if k < S.card then fourierCoeff f S ^ 2 else 0 := by
  -- Step 1: f x - lowDegreePart f k x = highDegreePart f k x
  have hfg : ∀ x, f x - lowDegreePart f k x = highDegreePart f k x := by
    intro x; linarith [low_plus_high_eq f k x]
  -- Step 2: l2DistSq = innerProduct (highDegreePart f k) (highDegreePart f k)
  have step2 : l2DistSq f (lowDegreePart f k) =
      innerProduct (highDegreePart f k) (highDegreePart f k) := by
    simp only [l2DistSq, innerProduct, expect]
    congr 1; congr 1; ext x
    rw [hfg x, sq]
  rw [step2, parseval]
  -- Step 3: compute fourierCoeff of highDegreePart
  congr 1; ext S
  rw [fourierCoeff_highDegreePart]
  split_ifs <;> simp

-- Step 09: Tail Fourier weight bound: sum_{|S|>k} fhat(S)^2 <= I[f] / k.
-- This is the key estimate: levels > k contribute at most I[f]/k to Parseval.
/-- For a positive integer cutoff `k`, Fourier weight above `k` is at most total influence divided by `k`. [OD14, Prop. 3.2]

**Proof sketch.** Compare each retained squared coefficient with its contribution to the degree-weighted formula for total influence, then sum. -/
lemma tail_fourier_weight_bound (f : BooleanFunc n) (k : ℕ) (hk : 0 < k) :
    (∑ S : Finset (Fin n), if k < S.card then fourierCoeff f S ^ 2 else 0) ≤
    totalInfluence f / k := by
  have hk' : (k : ℝ) > 0 := Nat.cast_pos.mpr hk
  rw [totalInfluence_eq_sum_sq_deg]
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro S _
  split_ifs with hS
  · -- k < S.card, so fhat(S)^2 ≤ S.card * fhat(S)^2 / k
    rw [le_div_iff₀ hk']
    have hle : (k : ℝ) ≤ S.card := by exact_mod_cast Nat.le_of_lt hS
    calc fourierCoeff f S ^ 2 * ↑k
        = ↑k * fourierCoeff f S ^ 2 := mul_comm _ _
      _ ≤ ↑S.card * fourierCoeff f S ^ 2 := by
          apply mul_le_mul_of_nonneg_right hle (sq_nonneg _)
  · -- S.card ≤ k, so LHS = 0
    positivity

-- Step 10: Combine steps 08 and 09 to get the L2 approximation theorem.
/-- Degree truncation at positive cutoff `k` has squared L² error at most total influence divided by `k`. [OD14, Prop. 3.2] -/
lemma lowDegree_approx (f : BooleanFunc n) (k : ℕ) (hk : 0 < k) :
    l2DistSq f (lowDegreePart f k) ≤ totalInfluence f / k := by
  rw [lowDegree_l2_error]
  exact tail_fourier_weight_bound f k hk

/-! ## Part IV: Influential coordinates bound -/

-- Step 11: The number of tau-influential coordinates is at most I[f] / tau.
/-- The number of coordinates with influence at least a positive threshold `τ` is at most total influence divided by `τ`. [OD14, Thm. 9.28]

**Proof sketch.** Sum the selected influences, each at least the threshold, and divide by the positive threshold. -/
lemma influential_coords_card (f : BooleanFunc n) (τ : ℝ) (hτ : 0 < τ) :
    ((influentialCoords f τ).card : ℝ) ≤ totalInfluence f / τ := by
  rw [le_div_iff₀ hτ]
  calc ((influentialCoords f τ).card : ℝ) * τ
      = (influentialCoords f τ).card • τ := by rw [nsmul_eq_mul]
    _ ≤ ∑ i ∈ influentialCoords f τ, influence i f := by
        apply Finset.card_nsmul_le_sum
        intro i hi
        exact (Finset.mem_filter.mp hi).2
    _ ≤ totalInfluence f := by
        simp only [totalInfluence]
        apply Finset.sum_le_univ_sum_of_nonneg
        intro i
        rw [influence_eq_sum_fourier]
        exact Finset.sum_nonneg (fun S _ => by split_ifs <;> positivity)

-- Step 12: The lowDegreePart restricted to influential coordinates is a junta.
-- More precisely, f_{<=k} depends only on the coordinates appearing in sets S with |S| <= k.
-- We state a simpler version: lowDegreePart is a junta on all n coordinates (trivially).
-- The real content is that we can restrict to influential coords.
/-- Restricting degree-at-most-`k` Fourier support to coordinates of influence at least `τ` yields a real-valued junta with squared L² error at most `nτ`. [OD14, §9.6]
This elementary finite-dimensional estimate retains the ambient dimension, unlike Theorem 9.28.

**Proof sketch.** Keep Fourier sets contained in the selected coordinates. Their parity characters depend only on those coordinates. Parseval expresses the discarded weight as squared coefficients on omitted sets. Charge each set to an omitted coordinate, then bound by the sum of omitted influences, each below the threshold. -/
lemma lowDegreePart_depends_on_influential (f : BooleanFunc n) (k : ℕ) (τ : ℝ) (hτ : 0 < τ) :
    ∃ g : BooleanFunc n,
      IsJunta g (influentialCoords f τ) ∧
      l2DistSq (lowDegreePart f k) g ≤ (n : ℝ) * τ := by
  let J := influentialCoords f τ
  let g : BooleanFunc n := fun x =>
    ∑ S : Finset (Fin n),
      if S.card ≤ k ∧ S ⊆ J then fourierCoeff f S * chiS S x else 0
  refine ⟨g, ?_, ?_⟩
  -- Part 1: IsJunta g J
  · intro x y hxy
    simp only [g]
    apply Finset.sum_congr rfl; intro S _
    split_ifs with h
    · congr 1; simp only [chiS]
      apply Finset.prod_congr rfl; intro i hi
      exact congrArg boolToSign (hxy i (h.2 hi))
    · rfl
  -- Part 2: l2DistSq (lowDegreePart f k) g ≤ n * τ
  · -- The difference lowDegreePart f k - g keeps only S with |S|≤k and S⊄J
    -- By Parseval, l2DistSq = ∑_{|S|≤k, S⊄J} fhat(S)^2
    -- Bound: ≤ ∑_{S⊄J} fhat(S)^2 ≤ ∑_{i∉J} ∑_{S∋i} fhat(S)^2 = ∑_{i∉J} Inf_i < n*τ
    -- We use a direct bound: l2DistSq ≤ innerProduct of the difference
    -- Step 1: Express the difference pointwise
    have hdiff : ∀ x, lowDegreePart f k x - g x =
        ∑ S : Finset (Fin n),
          if S.card ≤ k ∧ ¬S ⊆ J then fourierCoeff f S * chiS S x else 0 := by
      intro x
      simp only [lowDegreePart, g]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro S _
      by_cases h1 : S.card ≤ k <;> by_cases h2 : S ⊆ J <;> simp [h1, h2]
    -- Step 2: l2DistSq = innerProduct of difference = Parseval sum
    -- We bound l2DistSq directly
    have hbound : l2DistSq (lowDegreePart f k) g ≤
        ∑ S : Finset (Fin n),
          if ¬S ⊆ J then fourierCoeff f S ^ 2 else 0 := by
      simp only [l2DistSq]
      rw [show (fun x => (lowDegreePart f k x - g x) ^ 2) =
          (fun x => ((∑ S : Finset (Fin n),
            if S.card ≤ k ∧ ¬S ⊆ J then fourierCoeff f S * chiS S x else 0)) ^ 2) from
        funext (fun x => by rw [hdiff x])]
      -- The expect of squares of a Fourier sum = sum of squared coefficients (Parseval)
      -- This is: innerProduct h h = ∑_S (fourierCoeff h S)^2 where h is the diff
      -- h = ∑_{|S|≤k, S⊄J} fhat(S) * chiS S
      -- By Parseval: expect(h^2) = ∑_S (fourierCoeff h S)^2
      -- But fourierCoeff h S = fhat(S) when |S|≤k ∧ S⊄J, else 0
      -- So expect(h^2) = ∑_{|S|≤k, S⊄J} fhat(S)^2
      -- Then ≤ ∑_{S⊄J} fhat(S)^2 by adding nonneg terms
      -- Define h before using it
      set h : BooleanFunc n := fun x => ∑ S : Finset (Fin n),
          if S.card ≤ k ∧ ¬S ⊆ J then fourierCoeff f S * chiS S x else 0
      -- Step 1: expect(h^2) = innerProduct h h = ∑ fourierCoeff h S ^ 2
      have hh_eq : expect (fun x => (∑ S : Finset (Fin n),
            if S.card ≤ k ∧ ¬S ⊆ J then fourierCoeff f S * chiS S x else 0) ^ 2) =
          ∑ S : Finset (Fin n), fourierCoeff h S ^ 2 := by
        have inner_eq : expect (fun x => h x ^ 2) = innerProduct h h := by
          simp only [innerProduct]; congr 1; ext x; ring
        have goal_eq : expect (fun x => (∑ S : Finset (Fin n),
            if S.card ≤ k ∧ ¬S ⊆ J then fourierCoeff f S * chiS S x else 0) ^ 2) =
            expect (fun x => h x ^ 2) := rfl
        rw [goal_eq, inner_eq, parseval]
      rw [hh_eq]
      -- Step 2: Compute Fourier coefficients of h (same as fourierCoeff_lowDegreePart pattern)
      have hcoeff : ∀ T : Finset (Fin n),
          fourierCoeff h T = if T.card ≤ k ∧ ¬T ⊆ J then fourierCoeff f T else 0 := by
        intro T
        simp only [h]
        unfold BooleanAnalysis.fourierCoeff innerProduct expect
        beta_reduce
        set w := uniformWeight n
        set fhat : Finset (Fin n) → ℝ := fun S => w * ∑ y, f y * chiS S y
        -- Rearrange: w * ∑ x, (∑ S, if ... then fhat S * χ_S x else 0) * χ_T x
        have step1 : w * ∑ x, (∑ S : Finset (Fin n),
            if S.card ≤ k ∧ ¬S ⊆ J then fhat S * chiS S x else 0) * chiS T x =
            ∑ S : Finset (Fin n), if S.card ≤ k ∧ ¬S ⊆ J then
              fhat S * (w * ∑ x, chiS S x * chiS T x) else 0 := by
          rw [Finset.mul_sum]
          conv_lhs => arg 2; ext x; rw [Finset.sum_mul]
          simp_rw [show ∀ (S : Finset (Fin n)) (x : BoolCube n),
              (if S.card ≤ k ∧ ¬S ⊆ J then fhat S * chiS S x else 0) * chiS T x =
              (if S.card ≤ k ∧ ¬S ⊆ J then fhat S * (chiS S x * chiS T x) else 0) from by
            intros; split_ifs <;> ring]
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          congr 1; ext S
          split_ifs with hS
          · congr 1; ext x; ring
          · simp
        rw [step1]
        have ortho : ∀ S : Finset (Fin n),
            w * ∑ x, chiS S x * chiS T x = if S = T then 1 else 0 := by
          intro S
          have := fourier_coeff_chi S T
          simp only [innerProduct, expect] at this
          exact this
        simp_rw [ortho]
        simp only [mul_ite, mul_one, mul_zero]
        conv_lhs => arg 2; ext S; rw [show (if S.card ≤ k ∧ ¬S ⊆ J then
            (if S = T then fhat S else 0) else 0) =
            (if S = T then (if T.card ≤ k ∧ ¬T ⊆ J then fhat T else 0) else 0) from by
          split_ifs <;> simp_all]
        simp [Finset.sum_ite_eq', fhat]
      -- Step 3: Rewrite the Parseval sum using hcoeff
      conv_lhs => arg 2; ext S; rw [hcoeff S]
      -- Step 4: (if cond then c else 0)^2 = if cond then c^2 else 0
      conv_lhs => arg 2; ext S; rw [show (if S.card ≤ k ∧ ¬S ⊆ J then fourierCoeff f S else 0) ^ 2 =
          (if S.card ≤ k ∧ ¬S ⊆ J then fourierCoeff f S ^ 2 else 0) from by
        split_ifs <;> simp [sq]]
      -- Step 5: ∑_S (if |S|≤k ∧ S⊄J then fhat^2 else 0) ≤ ∑_S (if S⊄J then fhat^2 else 0)
      apply Finset.sum_le_sum
      intro S _
      by_cases hSJ : S ⊆ J
      · simp [hSJ]
      · by_cases hk : S.card ≤ k
        · simp [hk, hSJ]
        · simp only [hSJ, hk, not_false_eq_true, ↓reduceIte, false_and]
          exact sq_nonneg (fourierCoeff f S)
    -- Step 3: Union bound: ∑_{S⊄J} fhat(S)^2 ≤ ∑_{i∉J} Inf_i[f]
    have hunion : ∑ S : Finset (Fin n), (if ¬S ⊆ J then fourierCoeff f S ^ 2 else 0) ≤
        ∑ i ∈ Finset.univ.filter (fun i => i ∉ J), influence i f := by
      -- Rewrite RHS using influence_eq_sum_fourier
      simp_rw [influence_eq_sum_fourier]
      rw [Finset.sum_comm]
      apply Finset.sum_le_sum
      intro S _
      by_cases hS : S ⊆ J
      · -- S ⊆ J: LHS = 0
        rw [if_neg (not_not.mpr hS)]
        apply Finset.sum_nonneg
        intro i _
        by_cases hi : i ∈ S <;> simp [hi]; positivity
      · -- S ⊄ J
        rw [if_pos hS]
        obtain ⟨i, hiS, hiJ⟩ := Finset.not_subset.mp hS
        have hi_mem : i ∈ Finset.univ.filter (fun i => i ∉ J) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ i, hiJ⟩
        apply le_trans _ (Finset.single_le_sum (f := fun j => if j ∈ S then fourierCoeff f S ^ 2 else 0)
          (fun j _ => by by_cases hj : j ∈ S <;> simp [hj]; positivity) hi_mem)
        simp [hiS]
    -- Step 4: ∑_{i∉J} Inf_i < n * τ
    have hinfluence : ∑ i ∈ Finset.univ.filter (fun i => i ∉ J), influence i f ≤ n * τ := by
      calc ∑ i ∈ Finset.univ.filter (fun i => i ∉ J), influence i f
          ≤ ∑ _i ∈ Finset.univ.filter (fun i => i ∉ J), τ := by
            apply Finset.sum_le_sum; intro i hi
            have hni : i ∉ J := (Finset.mem_filter.mp hi).2
            simp only [J, influentialCoords, Finset.mem_filter, Finset.mem_univ, true_and] at hni
            linarith [lt_of_not_ge hni]
        _ ≤ n * τ := by
            rw [Finset.sum_const, nsmul_eq_mul]
            apply mul_le_mul_of_nonneg_right _ (le_of_lt hτ)
            have : (Finset.univ.filter (fun i => i ∉ J)).card ≤ (Finset.univ : Finset (Fin n)).card :=
              Finset.card_filter_le _ _
            simp at this
            exact_mod_cast this
    linarith [hbound, hunion, hinfluence]


/-- A finite set `s` has at most `(s.card + 1) ^ k` subsets of cardinality at most `k`,
including `k = 0`, when the empty set is the only such subset.
This elementary counting estimate is used in [OD14, Cor. 9.32].

**Proof sketch.** Partition the subsets by cardinality. The layer of size `i` has
binomial cardinality, bounded by `s.card ^ i`. Sum these bounds for `i ≤ k` and
bound the resulting geometric sum by `(s.card + 1) ^ k` using induction. -/
lemma card_bounded_subsets_le {α : Type*} [DecidableEq α] (s : Finset α) (k : ℕ) :
    (s.powerset.filter (fun t => t.card ≤ k)).card ≤ (s.card + 1) ^ k :=
  (by
  classical
  have hgeometric (j : ℕ) :
      (∑ i ∈ Finset.range (j + 1), s.card ^ i) ≤ (s.card + 1) ^ j := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Finset.sum_range_succ, pow_succ, pow_succ]
      have hpower := Nat.pow_le_pow_left (show s.card ≤ s.card + 1 by omega) j
      have hmul := mul_le_mul_of_nonneg_right hpower (show 0 ≤ s.card by omega)
      nlinarith only [ih, hmul]
  calc
    (s.powerset.filter (fun t => t.card ≤ k)).card ≤
        ((Finset.range (k + 1)).biUnion (fun i => Finset.powersetCard i s)).card := by
      apply Finset.card_le_card
      intro t ht
      obtain ⟨hts, htk⟩ := Finset.mem_filter.mp ht
      apply Finset.mem_biUnion.mpr
      refine ⟨t.card, Finset.mem_range.mpr (by omega), ?_⟩
      exact Finset.mem_powersetCard.mpr ⟨Finset.mem_powerset.mp hts, rfl⟩
    _ ≤ ∑ i ∈ Finset.range (k + 1), (Finset.powersetCard i s).card :=
      Finset.card_biUnion_le
    _ = ∑ i ∈ Finset.range (k + 1), s.card.choose i := by
      simp only [Finset.card_powersetCard]
    _ ≤ ∑ i ∈ Finset.range (k + 1), s.card ^ i :=
      Finset.sum_le_sum (fun i _ => Nat.choose_le_pow s.card i)
    _ ≤ (s.card + 1) ^ k := hgeometric k
)

end KKL
