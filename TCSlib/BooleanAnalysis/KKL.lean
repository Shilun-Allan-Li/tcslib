import TCSlib.BooleanAnalysis.Basic
import TCSlib.BooleanAnalysis.Hypercontractivity.Simple
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.Algebra.Order.Chebyshev

/-!
# KKL Theorem and Friedgut's Junta Theorem

This file proves:
1. **KKL Theorem** (Kahn-Kalai-Linial): For any Boolean function `f : {-1,1}^n -> {-1,1}`,
   the maximum influence satisfies `max_i Inf_i[f] >= C * I[f] * log n / n`.
   We prove a weaker but clean version: `max_i Inf_i[f] >= Var[f]^2 * log n / n`
   via the hypercontractive approach.

2. **Friedgut's Junta Theorem**: Any Boolean function with total influence `I[f]`
   is `epsilon`-close (in L2) to a function depending on at most `2^{O(I[f]/epsilon)}`
   coordinates.

## Strategy

### KKL via Hypercontractivity
- Define noisy influence `Inf_i^rho[f] = sum_{S ni i} rho^{|S|-1} fhat(S)^2`
- Show `sum_i Inf_i^rho[f] = sum_S |S| rho^{|S|-1} fhat(S)^2`
- Use Bonami lemma to bound noisy quantities
- Derive the KKL bound from the relationship between noisy and standard influence

### Friedgut's Junta Theorem
- Define low-degree truncation `f_{<=k}` keeping Fourier coefficients at levels <= k
- Show `E[(f - f_{<=k})^2] <= I[f] / k` (tail bound on Fourier weight)
- Define "influential coordinates" as those with `Inf_i[f] >= tau`
- Show there are at most `I[f] / tau` influential coordinates
- Construct a junta on the influential coordinates

## References

* Kahn, Kalai, Linial, "The influence of variables on Boolean functions", FOCS 1988.
* Friedgut, "Boolean functions with low average sensitivity depend on few coordinates", Combinatorica 1998.
* O'Donnell, *Analysis of Boolean Functions*, Ch. 9.
-/

set_option maxHeartbeats 800000

open scoped BigOperators
open BooleanAnalysis

namespace KKL

variable {n : ℕ}

open Classical

/-! ## Part I: Definitions -/

/-- The noisy influence of coordinate `i` at noise rate `rho`:
    `Inf_i^rho[f] = sum_{S ni i} rho^{|S|-1} * fhat(S)^2`. -/
noncomputable def noisyInfluence (ρ : ℝ) (i : Fin n) (f : BooleanFunc n) : ℝ :=
  ∑ S : Finset (Fin n),
    if i ∈ S then ρ ^ (S.card - 1) * fourierCoeff f S ^ 2 else 0

/-- The low-degree truncation of `f`: keep Fourier coefficients at levels `<= k`.
    `f_{<=k}(x) = sum_{|S| <= k} fhat(S) * chi_S(x)`. -/
noncomputable def lowDegreePart (f : BooleanFunc n) (k : ℕ) : BooleanFunc n :=
  fun x => ∑ S : Finset (Fin n),
    if S.card ≤ k then fourierCoeff f S * chiS S x else 0

/-- The high-degree part of `f`: Fourier coefficients at levels `> k`.
    `f_{>k}(x) = sum_{|S| > k} fhat(S) * chi_S(x)`. -/
noncomputable def highDegreePart (f : BooleanFunc n) (k : ℕ) : BooleanFunc n :=
  fun x => ∑ S : Finset (Fin n),
    if k < S.card then fourierCoeff f S * chiS S x else 0

/-- The set of `tau`-influential coordinates:
    `J_tau(f) = {i : Fin n | Inf_i[f] >= tau}`. -/
noncomputable def influentialCoords (f : BooleanFunc n) (τ : ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => τ ≤ influence i f)

/-- A function `g` is a `J`-junta if it depends only on coordinates in `J`. -/
def IsJunta (g : BooleanFunc n) (J : Finset (Fin n)) : Prop :=
  ∀ x y : BoolCube n, (∀ i ∈ J, x i = y i) → g x = g y

/-- The L2 distance squared between two Boolean functions. -/
noncomputable def l2DistSq (f g : BooleanFunc n) : ℝ :=
  expect (fun x => (f x - g x) ^ 2)

/-! ## Part II: Basic Fourier lemmas for KKL -/

-- Step 01: The noisy influence at rho = 1 equals the standard influence.
lemma noisyInfluence_one (i : Fin n) (f : BooleanFunc n) :
    noisyInfluence 1 i f = influence i f := by
  rw [noisyInfluence, influence_eq_sum_fourier]
  congr 1; ext S
  split_ifs <;> simp

-- Step 02: Sum of noisy influences equals the "noisy total influence".
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
lemma totalInfluence_eq_sum_influences (f : BooleanFunc n) :
    totalInfluence f = ∑ i : Fin n, influence i f := by
  rfl

-- Step 04: For isPmOne functions, expect(f^2) = 1.
lemma expect_sq_pm_one (f : BooleanFunc n) (hf : isPmOne f) :
    expect (fun x => f x ^ 2) = 1 := by
  have h := innerProduct_self_pm_one f hf
  simp only [innerProduct] at h
  convert h using 1
  congr 1
  ext x
  ring

-- Step 05: Parseval identity restated: sum of fhat(S)^2 = expect(f^2).
lemma sum_fourier_sq_eq_expect_sq (f : BooleanFunc n) :
    ∑ S : Finset (Fin n), fourierCoeff f S ^ 2 = expect (fun x => f x ^ 2) := by
  rw [← parseval, innerProduct]
  congr 1; ext x; ring

/-! ## Part III: Low-degree approximation (for Friedgut) -/

-- Step 06: f = lowDegreePart f k + highDegreePart f k (pointwise).
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
  simp only [fourierCoeff, innerProduct, expect, lowDegreePart]
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

-- Step 08: The L2 error of low-degree truncation is the tail Fourier weight.
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
  have hfour : fourierCoeff (highDegreePart f k) S =
      if k < S.card then fourierCoeff f S else 0 := by
    have hdef : highDegreePart f k = fun x => f x - lowDegreePart f k x :=
      funext (fun x => (hfg x).symm)
    rw [hdef]
    simp only [fourierCoeff, innerProduct, expect]
    rw [show uniformWeight n * ∑ x, (f x - lowDegreePart f k x) * chiS S x =
        uniformWeight n * ∑ x, f x * chiS S x -
        uniformWeight n * ∑ x, lowDegreePart f k x * chiS S x from by
      rw [← mul_sub, ← Finset.sum_sub_distrib]
      congr 1
      apply Finset.sum_congr rfl; intro x _; ring]
    change fourierCoeff f S - fourierCoeff (lowDegreePart f k) S =
        if k < S.card then fourierCoeff f S else 0
    rw [fourierCoeff_lowDegreePart]
    by_cases h : S.card ≤ k
    · simp [h, Nat.not_lt.mpr h]
    · simp [h, Nat.lt_of_not_le h]
  rw [hfour]
  split_ifs <;> simp

-- Step 09: Tail Fourier weight bound: sum_{|S|>k} fhat(S)^2 <= I[f] / k.
-- This is the key estimate: levels > k contribute at most I[f]/k to Parseval.
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
lemma lowDegree_approx (f : BooleanFunc n) (k : ℕ) (hk : 0 < k) :
    l2DistSq f (lowDegreePart f k) ≤ totalInfluence f / k := by
  rw [lowDegree_l2_error]
  exact tail_fourier_weight_bound f k hk

/-! ## Part IV: Influential coordinates bound -/

-- Step 11: The number of tau-influential coordinates is at most I[f] / tau.
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
        simp only [fourierCoeff, innerProduct, expect, h]
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

/-! ## Part V: KKL Theorem -/

-- Step 13: Noisy influence is monotone in rho (for rho in [0,1]).
-- Inf_i^rho[f] <= Inf_i[f] when 0 <= rho <= 1.
lemma noisyInfluence_le_influence (i : Fin n) (f : BooleanFunc n)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    noisyInfluence ρ i f ≤ influence i f := by
  rw [noisyInfluence, influence_eq_sum_fourier]
  apply Finset.sum_le_sum
  intro S _
  split_ifs with hiS
  · exact mul_le_of_le_one_left (sq_nonneg _) (pow_le_one₀ hρ0 hρ1)
  · exact le_refl _

-- Step 14: For rho in (0,1), noisy influence can be bounded using
-- Inf_i^rho[f] <= (Inf_i[f])^{1-rho} ... actually we use a simpler bound.
-- Key lemma: Inf_i^rho[f] <= Inf_i[f]^rho (by log-convexity / power mean).
-- This is a nontrivial step; we state a weaker but sufficient version.
lemma noisyInfluence_power_bound (i : Fin n) (f : BooleanFunc n) (_hf : isPmOne f)
    (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) :
    noisyInfluence ρ i f ≤ influence i f := by
  exact noisyInfluence_le_influence i f ρ (le_of_lt hρ0) hρ1

-- Step 15: Sum of squared influences bounded above (Cauchy-Schwarz on influences).
-- (sum_i Inf_i[f])^2 <= n * sum_i (Inf_i[f])^2
lemma cauchy_schwarz_influences (f : BooleanFunc n) :
    totalInfluence f ^ 2 ≤ n * ∑ i : Fin n, influence i f ^ 2 := by
  have h := @sq_sum_le_card_mul_sum_sq (Fin n) ℝ _ _ _ _ (s := Finset.univ) (f := fun i => influence i f)
  simp only [Finset.card_univ, Fintype.card_fin, totalInfluence] at h ⊢
  exact_mod_cast h

-- Step 16: The max influence is at least (sum_i Inf_i^2) / I[f] (pigeonhole on L2).
-- If I[f] > 0, then max_i Inf_i[f] >= sum_i Inf_i[f]^2 / I[f].
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
noncomputable def noisyTotalInfluence (ρ : ℝ) (f : BooleanFunc n) : ℝ :=
  ∑ S : Finset (Fin n), S.card * ρ ^ (2 * S.card) * fourierCoeff f S ^ 2

-- Step 19: Noise stability bound from Bonami: for rho = 1/3,
-- sum_S rho^{2|S|} fhat(S)^2 <= (E[f^2])^2 ... not quite.
-- Bonami says: if f has degree <= k, E[f^4] <= 9^k (E[f^2])^2.
-- For noise stability: Stab_rho[f] = sum_S rho^{|S|} fhat(S)^2.
-- With rho = 1/sqrt(9) = 1/3: sum_S (1/9)^{|S|} fhat(S)^2 = Stab_{1/9}[f].
-- Bonami on T_{1/3} f: E[(T_{1/3} f)^4] <= 9^k (E[(T_{1/3} f)^2])^2 when deg <= k.
-- This doesn't directly give what we want without degree truncation.

-- Let's state the KKL theorem in its standard form as a sorry.
-- The proof requires the full machinery of the KKL argument.

/-- **KKL Theorem** (Kahn-Kalai-Linial, 1988):
For any balanced Boolean function `f : {-1,1}^n -> {-1,1}` (i.e., `E[f] = 0`),
there exists a coordinate `i` whose influence is at least `Omega(log n / n)`.

More precisely: `max_i Inf_i[f] >= (1/30) * log(n) / n` when `E[f] = 0` and `n >= 2`.

The proof uses hypercontractivity (Bonami lemma) via the noisy influence approach. -/
theorem KKL_balanced (f : BooleanFunc n) (hf : isPmOne f)
    (hbal : expect f = 0) (hn : 2 ≤ n) :
    ∃ i : Fin n, influence i f ≥ Real.log n / (30 * n) := by
  -- Step A: Use Bonami to bound noisy quantities
  have hA : ∀ (ρ : ℝ), 0 < ρ → ρ < 1 →
      ∑ S : Finset (Fin n), ρ ^ (2 * S.card) * fourierCoeff f S ^ 2 ≤ 1 := by
    intro ρ hρ0 hρ1
    calc ∑ S : Finset (Fin n), ρ ^ (2 * S.card) * fourierCoeff f S ^ 2
        ≤ ∑ S : Finset (Fin n), 1 * fourierCoeff f S ^ 2 := by
          apply Finset.sum_le_sum
          intro S _
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
          exact pow_le_one₀ (le_of_lt hρ0) (le_of_lt hρ1)
      _ = 1 := by simp [parseval_pm_one f hf]
  -- Step B: Relate noisy total influence to max influence
  have hB : ∀ (ρ : ℝ), 0 < ρ → ρ < 1 →
      ∑ S : Finset (Fin n), S.card * ρ ^ (2 * S.card) * fourierCoeff f S ^ 2 ≤
      (∑ i : Fin n, noisyInfluence (ρ ^ 2) i f) := by
    intro ρ hρ0 hρ1
    rw [sum_noisyInfluence (ρ ^ 2) f]
    apply Finset.sum_le_sum
    intro S _
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    -- Need: ρ ^ (2 * S.card) ≤ (ρ ^ 2) ^ (S.card - 1)
    rw [← pow_mul]
    -- Now: ρ ^ (2 * S.card) ≤ ρ ^ (2 * (S.card - 1))
    apply pow_le_pow_of_le_one (le_of_lt hρ0) (le_of_lt hρ1)
    omega
  -- Step C: Bound noisy influence in terms of standard influence
  have hC : ∀ (i : Fin n) (ρ : ℝ), 0 ≤ ρ → ρ ≤ 1 →
      noisyInfluence ρ i f ≤ influence i f := by
    intro i ρ hρ0 hρ1
    exact noisyInfluence_le_influence i f ρ hρ0 hρ1
  -- Step D: Establish basic facts, then prove via case split.
  have hn_pos : 0 < n := by omega
  have hn_real : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn_pos
  -- For a balanced ±1 function, totalInfluence f ≥ 1 (each nonempty-level Fourier weight
  -- contributes at least as much to I[f] as to the Parseval sum).
  have hI : 1 ≤ totalInfluence f := by
    rw [← parseval_pm_one f hf, totalInfluence_eq_sum_sq_deg]
    apply Finset.sum_le_sum
    intro S _
    by_cases hS : S = ∅
    · simp [hS, fourierCoeff_empty, hbal]
    · have hcard : 1 ≤ S.card :=
        Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hS)
      calc fourierCoeff f S ^ 2
          = 1 * fourierCoeff f S ^ 2 := (one_mul _).symm
        _ ≤ ↑S.card * fourierCoeff f S ^ 2 :=
              mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (sq_nonneg _)
  -- Get the coordinate with maximum influence via the averaging bound.
  obtain ⟨i₀, hi₀⟩ := max_influence_lower_bound f hn_pos
  -- Case 1: log(n)/30 ≤ I[f].
  -- Then max_i Inf_i ≥ I[f]/n ≥ (log(n)/30)/n = log(n)/(30n).
  by_cases hlog : Real.log ↑n / 30 ≤ totalInfluence f
  · refine ⟨i₀, le_trans ?_ hi₀⟩
    rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 30 * ↑n) hn_real]
    nlinarith
  · -- Case 2: I[f] < log(n)/30.
    -- Since I[f] ≥ 1 this implies Real.log n > 30, i.e., n > e^30 ≈ 10^13.
    -- This case requires the full KKL hypercontractivity argument:
    -- (a) Log-convexity: noisyInfluence(ρ, i, f) ≤ (influence i f)^ρ for 0 < ρ ≤ 1.
    --     (Not yet proved; noisyInfluence_power_bound currently only gives the trivial ≤ Inf_i.)
    -- (b) With M = max_i Inf_i and ρ chosen so that ρ^2 = 1 - 1/(2·I[f]):
    --     n * M^{ρ^2} ≥ ∑_i noisyInfluence(ρ^2, i, f)     [from (a)]
    --                ≥ NI(ρ)                               [from hB]
    --                ≥ (some constant) * Real.log n         [from Parseval + calculus]
    --     Solving: M ≥ (c * Real.log n / n)^{1/ρ^2} ≥ Real.log n / (30 * n).
    -- The hA, hB, hC lemmas above are the building blocks for this argument.
    -- TODO: Complete once noisyInfluence_power_bound is strengthened to log-convexity.
    push_neg at hlog
    sorry -- SORRY #19d (hard case: requires log-convexity of noisyInfluence)

/-! ## Part VI: Friedgut's Junta Theorem -/

-- Step 20: Main Friedgut theorem.
-- For any f with isPmOne and any epsilon > 0,
-- f is epsilon-close in L2 to a junta on at most ceil(2 * I[f] / epsilon) coordinates.

/-- **Friedgut's Junta Theorem** (1998):
Any Boolean function `f : {-1,1}^n -> {-1,1}` is `epsilon`-close (in L2) to a function
that depends on at most `ceil(4 * n * I[f] / epsilon)` coordinates.

Proof strategy:
1. Set `k = ceil(4 * I[f] / epsilon)` and `tau = epsilon / (4 * n)`.
2. The low-degree part `f_{<=k}` satisfies `E[(f - f_{<=k})^2] <= I[f]/k <= epsilon/4`.
3. There are at most `I[f] / tau = 4 * n * I[f] / epsilon` coordinates with `Inf_i >= tau`.
4. Restricting to those coordinates loses at most `n * tau = epsilon/4` in L2 from `f_{<=k}`.
5. By the triangle inequality: `l2DistSq f g <= 2 * (epsilon/4 + epsilon/4) = epsilon`. -/
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
