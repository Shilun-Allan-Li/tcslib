/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import TCSlib.BooleanAnalysis.Hypercontractivity.Cube.General.TwoPoint

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# General cube hypercontractivity

This is one stage of the forward hypercontractivity proof on the uniform Boolean cube.

## Main definitions

Shared definitions are imported; local technical helpers accompany their proofs.

## Main results

* `low_norms_hypercontractivity`.
* `high_norms_hypercontractivity`.
* `general_one_function_hypercontractivity`.
* `general_two_function_hypercontractivity`.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014, §§9.3–10.1.
-/

open BooleanAnalysis MeasureTheory Set Filter ProbabilityTheory Real
open scoped BigOperators ENNReal Classical

namespace BooleanAnalysis.Hypercontractivity

variable {n : ℕ}

/--
**Low Norms Hypercontractivity.**
For `1 < p ≤ u ≤ 2` and `ρ = √((p-1)/(u-1))`:
  `(𝔼[|T_ρ f|^u])^{1/u} ≤ (𝔼[|f|^p])^{1/p}`
**Source:** [OD14, §10.1].

**Proof sketch.** Equal exponents use same-exponent contraction; output exponent two uses the
bridging estimate. Otherwise combine the one-bit low-exponent estimate with Hölder, tensorize
the resulting pairing bound, and recover the output norm by a Hölder extremizer.
-/
theorem low_norms_hypercontractivity {n : ℕ}
    (p u : ℝ) (hp : 1 < p) (hpu : p ≤ u) (hu : u ≤ 2)
    (f : BooleanFunc n) :
    (expect (fun x => |noiseOp (Real.sqrt ((p - 1) / (u - 1))) f x| ^ u)) ^ (1 / u) ≤
    (expect (fun x => |f x| ^ p)) ^ (1 / p) := by
  set ρ := Real.sqrt ((p - 1) / (u - 1)) with hρ_def
  have hu1 : 1 < u := lt_of_lt_of_le hp hpu
  have hp_sub : 0 < p - 1 := by linarith
  have hu_sub : 0 < u - 1 := by linarith
  have hρ_sq : ρ ^ 2 = (p - 1) / (u - 1) := by
    rw [hρ_def]; exact Real.sq_sqrt (div_nonneg hp_sub.le hu_sub.le)
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρ1 : ρ ≤ 1 := Interpolation.sqrt_div_le_one hp_sub.le hu_sub (by linarith)
  -- Case 1: p = u (trivial contractivity)
  by_cases h_eq : p = u
  · subst h_eq
    have hρ_eq_1 : ρ = 1 := by rw [hρ_def]; simp [div_self (ne_of_gt hu_sub)]
    rw [hρ_eq_1]
    exact trivial_contractivity p (by linarith) 1 (by norm_num) (by norm_num) f  -- p > 1 ≥ 1
  · have hpu_strict : p < u := lt_of_le_of_ne hpu h_eq
    -- Case 2: u = 2 (bridging case applies directly)
    by_cases hu2 : u = 2
    · subst hu2
      exact bridging_hypercontractivity p 2 (by linarith) (by linarith) (by norm_num) f
    · -- Case 3: p < u < 2
      -- This requires the general two-point inequality for (p, u) norms.
      -- The proof proceeds by induction on n using a one-bit base case.
            -- Step 1: One-bit one-function
      have h_one_bit : ∀ g : BooleanFunc 1,
          (expect (fun x => |noiseOp ρ g x| ^ u)) ^ (1 / u) ≤
          (expect (fun x => |g x| ^ p)) ^ (1 / p) := by
        intro g; exact low_norms_one_bit p u hp hpu hu g
      -- Step 2: One-bit two-function (via Hölder)
      have h_two_func_one : ∀ (f' g' : BooleanFunc 1),
          innerProduct f' (noiseOp ρ g') ≤
          (expect (fun x => |f' x| ^ (u / (u - 1)))) ^ ((u - 1) / u) *
          (expect (fun x => |g' x| ^ p)) ^ (1 / p) := by
        intros f' g';
        refine' le_trans _ ( mul_le_mul_of_nonneg_left ( h_one_bit g' ) ( Real.rpow_nonneg ( expect_rpow_abs_nonneg _ _ ) _ ) );
        convert holder_ineq_bool ( u / ( u - 1 ) ) ( by rw [ lt_div_iff₀ ] <;> linarith ) f' ( noiseOp ρ g' ) using 1;
        grind  -- Hölder + h_one_bit
      -- Step 3: N-bit two-function (via hypercontractivity_induction)
      have hu' : 1 ≤ u / (u - 1) := le_div_iff₀ hu_sub |>.mpr (by linarith)
      have h_two_func_n : ∀ (f' g' : BooleanFunc n),
          innerProduct f' (noiseOp ρ g') ≤
          (expect (fun x => |f' x| ^ (u / (u - 1)))) ^ ((u - 1) / u) *
          (expect (fun x => |g' x| ^ p)) ^ (1 / p) := by
        intro f' g'
        have h_base : ∀ (f₁ g₁ : BooleanFunc 1),
            innerProduct f₁ (noiseOp ρ g₁) ≤
            (expect (fun x => |f₁ x| ^ (u / (u - 1)))) ^ (1 / (u / (u - 1))) *
            (expect (fun x => |g₁ x| ^ p)) ^ (1 / p) := by
          intro f₁ g₁
          convert h_two_func_one f₁ g₁ using 2; congr 1; field_simp
        convert hypercontractivity_induction (u / (u - 1)) p hu' (by linarith) ρ hρ0 hρ1 h_base f' g' using 2
        congr 1; field_simp
      -- Step 4: N-bit one-function (via Hölder sharpness)
      obtain ⟨f', hf'_norm, hf'_inner⟩ : ∃ f' : BooleanFunc n,
          (expect (fun x => |f' x| ^ (u / (u - 1)))) ^ ((u - 1) / u) ≤ 1 ∧
          (expect (fun x => |noiseOp ρ f x| ^ u)) ^ (1 / u) ≤ innerProduct f' (noiseOp ρ f) := by
        have := @holder_sharpness n (u / (u - 1)) u ?_ (noiseOp ρ f)
        · obtain ⟨f', hf'₁, hf'₂⟩ := this; use f'
          refine ⟨?_, hf'₂⟩
          have : (1 : ℝ) / (u / (u - 1)) = (u - 1) / u := by field_simp
          rwa [this] at hf'₁
        · constructor <;> norm_num
          · rw [inv_eq_one_div, ← add_div, div_eq_iff] <;> linarith
          · exact div_pos (by linarith) (by linarith)
          · linarith
      exact hf'_inner.trans (le_trans (h_two_func_n f' f)
        (mul_le_of_le_one_left (Real.rpow_nonneg (by
          rw [expect_eq_fintypeExpect]
          exact Finset.expect_nonneg fun _ _ ↦ by positivity) _) hf'_norm))
/--
**High Norms Hypercontractivity.**
For `2 ≤ p ≤ u` and `ρ ≤ √((p-1)/(u-1))`:
  `(𝔼[|T_ρ f|^u])^{1/u} ≤ (𝔼[|f|^p])^{1/p}`
Proof by duality: translating to the Hölder-conjugate exponents `u' ≤ p' ≤ 2`
and applying the low-norms case.
**Source:** [OD14, §10.1; Prop. 10.4].

**Proof sketch.** Pass to conjugate exponents u′ ≤ p′ ≤ 2, for which the sharp correlation is
unchanged. Apply the low-exponent estimate and operator duality. Obtain smaller correlations by
composing with same-exponent contraction.
-/
theorem high_norms_hypercontractivity {n : ℕ}
    (p u : ℝ) (hp : 2 ≤ p) (hpu : p ≤ u)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (_hρ1 : ρ ≤ 1)
    (hρ_bound : ρ ≤ Real.sqrt ((p - 1) / (u - 1)))
    (f : BooleanFunc n) :
    (expect (fun x => |noiseOp ρ f x| ^ u)) ^ (1 / u) ≤
    (expect (fun x => |f x| ^ p)) ^ (1 / p) := by
  set p' := p / (p - 1) with hp'_def
  set u' := u / (u - 1) with hu'_def
  have hp1 : 1 < p := by linarith
  have hu1 : 1 < u := by linarith
  have hp_sub : 0 < p - 1 := by linarith
  have hu_sub : 0 < u - 1 := by linarith
  have hp'_gt1 : 1 < p' := by rw [hp'_def, lt_div_iff₀ hp_sub]; linarith
  have hp'_le2 : p' ≤ 2 := by rw [hp'_def, div_le_iff₀ hp_sub]; linarith
  have hu'_gt1 : 1 < u' := by rw [hu'_def, lt_div_iff₀ hu_sub]; linarith
  have hu'_le_p' : u' ≤ p' := by
    rw [hu'_def, hp'_def, div_le_div_iff₀ hu_sub hp_sub]; nlinarith
  have h_conj_param : (p - 1) / (u - 1) = (u' - 1) / (p' - 1) := by
    rw [hp'_def, hu'_def]; field_simp; ring
  set ρ₀ := Real.sqrt ((p - 1) / (u - 1))
  have hρ₀0 : 0 ≤ ρ₀ := Real.sqrt_nonneg _
  have hρ₀1 : ρ₀ ≤ 1 := Interpolation.sqrt_div_le_one hp_sub.le hu_sub (by linarith)
  -- Low norms: ‖T_{ρ₀}‖_{u'→p'} ≤ 1
  have h_low : ∀ g : BooleanFunc n,
      (expect (fun x => |noiseOp ρ₀ g x| ^ p')) ^ (1 / p') ≤
      (expect (fun x => |g x| ^ u')) ^ (1 / u') := by
    intro g
    rw [show ρ₀ = Real.sqrt ((u' - 1) / (p' - 1)) from by rw [← h_conj_param]]
    exact low_norms_hypercontractivity u' p' hu'_gt1 hu'_le_p' hp'_le2 g
  -- Duality
  have h_dual := (noise_op_norm_dual u' p' hu'_gt1 hp'_gt1 ρ₀ hρ₀0 hρ₀1).mp h_low
  have h_ρ₀_result : (expect (fun x => |noiseOp ρ₀ f x| ^ u)) ^ (1 / u) ≤
      (expect (fun x => |f x| ^ p)) ^ (1 / p) := by
    have h := h_dual f
    have hp'_conj : p' / (p' - 1) = p := by rw [hp'_def]; field_simp; ring
    have hu'_conj : u' / (u' - 1) = u := by rw [hu'_def]; field_simp; ring
    have hp'_exp : (p' - 1) / p' = 1 / p := by rw [hp'_def]; field_simp; ring
    have hu'_exp : (u' - 1) / u' = 1 / u := by rw [hu'_def]; field_simp; ring
    rw [hp'_conj, hu'_conj, hp'_exp, hu'_exp] at h
    exact h
  -- For ρ ≤ ρ₀: composition + contractivity
  by_cases hρ₀_zero : ρ₀ = 0
  · have : ρ = 0 := le_antisymm (by rw [← hρ₀_zero]; exact hρ_bound) hρ0
    rw [this]; rw [hρ₀_zero] at h_ρ₀_result; exact h_ρ₀_result
  · have hρ₀_pos : 0 < ρ₀ := lt_of_le_of_ne hρ₀0 (Ne.symm hρ₀_zero)
    have h_compose : noiseOp ρ f = noiseOp (ρ / ρ₀) (noiseOp ρ₀ f) := by
      rw [noiseOp_compose, div_mul_cancel₀ _ (ne_of_gt hρ₀_pos)]
    have h_contract := trivial_contractivity u (by linarith : 1 ≤ u)
      (ρ / ρ₀) (div_nonneg hρ0 hρ₀0) (by rwa [div_le_one hρ₀_pos]) (noiseOp ρ₀ f)
    calc (expect (fun x => |noiseOp ρ f x| ^ u)) ^ (1 / u)
        = (expect (fun x => |noiseOp (ρ / ρ₀) (noiseOp ρ₀ f) x| ^ u)) ^ (1 / u) := by
          rw [h_compose]
      _ ≤ (expect (fun x => |noiseOp ρ₀ f x| ^ u)) ^ (1 / u) := h_contract
      _ ≤ (expect (fun x => |f x| ^ p)) ^ (1 / p) := h_ρ₀_result

/-! ## General One-Function Hypercontractivity -/

/-
**General One-Function Hypercontractivity Theorem.**
For `1 ≤ p ≤ u` with `u > 1` and `ρ ≤ √((p-1)/(u-1))`:
  `(𝔼[|T_ρ f|^u])^{1/u} ≤ (𝔼[|f|^p])^{1/p}`

Combines the three cases:
- Bridging: `1 ≤ p ≤ 2 ≤ u`
- Low norms: `1 < p ≤ u ≤ 2`
- High norms: `2 ≤ p ≤ u`
-/
/-- Cube noise contracts the `p` norm to the `u` norm for finite `1 ≤ p ≤ u`, `u > 1`,
and `0 ≤ ρ ≤ √((p-1)/(u-1))`.
This is the finite-exponent specialization of the source's Hypercontractivity Theorem.
The source's infinite-exponent endpoints are not represented here; the finite `p = u = 1`
case is covered separately by `trivial_contractivity`.

**Source:** [OD14, §10.1; Prop. 10.4].

**Proof sketch.** Separate the exponent ranges below, across, and above two and use the low-
exponent, bridging, or high-exponent estimate. Obtain smaller correlations by noise composition
and same-exponent contraction. For p = 1 below the bridging range, correlation vanishes and the
expectation triangle inequality applies.
-/
theorem general_one_function_hypercontractivity {n : ℕ}
    (p u : ℝ) (hp : 1 ≤ p) (hpu : p ≤ u) (hu1 : 1 < u)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hρ_bound : ρ ≤ Real.sqrt ((p - 1) / (u - 1)))
    (f : BooleanFunc n) :
    (expect (fun x => |noiseOp ρ f x| ^ u)) ^ (1 / u) ≤
    (expect (fun x => |f x| ^ p)) ^ (1 / p) := by
  by_cases hp2 : p ≤ 2
  · by_cases hu2 : 2 ≤ u
    · -- Case 1: 1 ≤ p ≤ 2 ≤ u (bridging + composition)
      set ρ₀ := Real.sqrt ((p - 1) / (u - 1))
      have hρ₀0 : 0 ≤ ρ₀ := Real.sqrt_nonneg _
      have hu_sub : 0 < u - 1 := by linarith
      have hρ₀1 : ρ₀ ≤ 1 := Interpolation.sqrt_div_le_one (by linarith) hu_sub (by linarith)
      by_cases hρ₀_zero : ρ₀ = 0
      · have hρz : ρ = 0 := le_antisymm (by rw [← hρ₀_zero]; exact hρ_bound) hρ0
        simp only [hρz]; show _ ≤ _
        rw [show (0 : ℝ) = ρ₀ from hρ₀_zero.symm]
        exact bridging_hypercontractivity p u hp hp2 hu2 f
      · have hρ₀_pos : 0 < ρ₀ := lt_of_le_of_ne hρ₀0 (Ne.symm hρ₀_zero)
        have h_compose : noiseOp ρ f = noiseOp (ρ / ρ₀) (noiseOp ρ₀ f) := by
          rw [noiseOp_compose, div_mul_cancel₀ _ (ne_of_gt hρ₀_pos)]
        have h_contract := trivial_contractivity u (by linarith : 1 ≤ u)
          (ρ / ρ₀) (div_nonneg hρ0 hρ₀0) (by rwa [div_le_one hρ₀_pos]) (noiseOp ρ₀ f)
        calc (expect (fun x => |noiseOp ρ f x| ^ u)) ^ (1 / u)
            = (expect (fun x => |noiseOp (ρ / ρ₀) (noiseOp ρ₀ f) x| ^ u)) ^ (1 / u) := by
              rw [h_compose]
          _ ≤ (expect (fun x => |noiseOp ρ₀ f x| ^ u)) ^ (1 / u) := h_contract
          _ ≤ (expect (fun x => |f x| ^ p)) ^ (1 / p) :=
              bridging_hypercontractivity p u hp hp2 hu2 f
    · -- Case 2: 1 ≤ p ≤ u ≤ 2 (low norms)
      push_neg at hu2
      rcases eq_or_lt_of_le hp with rfl | hp1
      · -- p = 1 edge case: ρ = 0 and T_0 f is constant = E[f]
        simp only [sub_self, zero_div, Real.sqrt_zero] at hρ_bound
        have hρ_zero : ρ = 0 := le_antisymm hρ_bound hρ0
        subst hρ_zero
        -- T_0 f(x) = f̂(∅) for all x, so |T_0 f|^u is constant.
        -- By Jensen: E[|const|^u]^{1/u} = |const| ≤ E[|f|]^1
        -- This is trivial contractivity at s = u ≥ 1 with ρ = 0
        -- T_0 f is constant = E[f], so |T_0 f(x)|^u = |E[f]|^u.
        -- |E[f]| ≤ E[|f|] = ‖f‖_1 by triangle inequality.
        unfold noiseOp; norm_num;
        simp +decide [zero_pow_eq ];
        unfold expect; norm_num [ uniformWeight ] ;
        rw [ ← mul_assoc, ← mul_pow ] ; norm_num [ show u ≠ 0 by linarith ];
        unfold fourierCoeff;
        unfold innerProduct; norm_num [ uniformWeight ] ;
        unfold expect; norm_num [ uniformWeight ] ;
        exact Finset.abs_sum_le_sum_abs _ _ -- Edge case: p = 1, ρ = 0
      -- low_norms gives the bound with ρ = sqrt((p-1)/(u-1))
      -- For ρ ≤ that value, use composition + contractivity
      set ρ₀ := Real.sqrt ((p - 1) / (u - 1))
      have hρ₀0 : 0 ≤ ρ₀ := Real.sqrt_nonneg _
      have hu_sub : 0 < u - 1 := by linarith
      have hρ₀1 : ρ₀ ≤ 1 := Interpolation.sqrt_div_le_one (by linarith) hu_sub (by linarith)
      have h_low : ∀ g : BooleanFunc n,
          (expect (fun x => |noiseOp ρ₀ g x| ^ u)) ^ (1 / u) ≤
          (expect (fun x => |g x| ^ p)) ^ (1 / p) :=
        fun g => low_norms_hypercontractivity p u hp1 hpu (le_of_lt hu2) g
      by_cases hρ₀_zero : ρ₀ = 0
      · have : ρ = 0 := le_antisymm (by rw [← hρ₀_zero]; exact hρ_bound) hρ0
        rw [this]; rw [hρ₀_zero] at h_low; exact h_low f
      · have hρ₀_pos : 0 < ρ₀ := lt_of_le_of_ne hρ₀0 (Ne.symm hρ₀_zero)
        have h_compose : noiseOp ρ f = noiseOp (ρ / ρ₀) (noiseOp ρ₀ f) := by
          rw [noiseOp_compose, div_mul_cancel₀ _ (ne_of_gt hρ₀_pos)]
        have h_contract := trivial_contractivity u (by linarith : 1 ≤ u)
          (ρ / ρ₀) (div_nonneg hρ0 hρ₀0) (by rwa [div_le_one hρ₀_pos]) (noiseOp ρ₀ f)
        calc (expect (fun x => |noiseOp ρ f x| ^ u)) ^ (1 / u)
            = (expect (fun x => |noiseOp (ρ / ρ₀) (noiseOp ρ₀ f) x| ^ u)) ^ (1 / u) := by
              rw [h_compose]
          _ ≤ (expect (fun x => |noiseOp ρ₀ f x| ^ u)) ^ (1 / u) := h_contract
          _ ≤ (expect (fun x => |f x| ^ p)) ^ (1 / p) := h_low f
  · -- Case 3: 2 ≤ p ≤ u (high norms)
    push_neg at hp2
    exact high_norms_hypercontractivity p u (le_of_lt hp2) hpu ρ hρ0 hρ1 hρ_bound f

/-! ## General Two-Function Hypercontractivity -/

/--
**General Two-Function Hypercontractivity Theorem.**
For finite `1 ≤ p ≤ u` with `u ≥ 2` and `0 ≤ ρ ≤ √((p-1)/(u-1))`:
  `⟨f, T_ρ g⟩ ≤ (𝔼[|f|^{u/(u-1)}])^{(u-1)/u} · (𝔼[|g|^p])^{1/p}`

Derived from the one-function theorem via `one_function_iff_two_function_hypercontractivity`.
This finite cube parameterization does not assert the source's infinite-exponent endpoints
or every parameter case of its abstract two-function formulation.
**Source:** [OD14, §10.1; Prop. 10.4]. -/
theorem general_two_function_hypercontractivity {n : ℕ}
    (p u : ℝ) (hp : 1 ≤ p) (hpu : p ≤ u) (hu : 2 ≤ u)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hρ_bound : ρ ≤ Real.sqrt ((p - 1) / (u - 1)))
    (f g : BooleanFunc n) :
    innerProduct f (noiseOp ρ g) ≤
    (expect (fun x => |f x| ^ (u / (u - 1)))) ^ ((u - 1) / u) *
    (expect (fun x => |g x| ^ p)) ^ (1 / p) := by
  have hu1 : 1 < u := by linarith
  exact ((one_function_iff_two_function_hypercontractivity p u hp hpu hu ρ hρ0 hρ1 hρ_bound).mp
    (fun f' => general_one_function_hypercontractivity p u hp hpu hu1 ρ hρ0 hρ1 hρ_bound f')) f g

end BooleanAnalysis.Hypercontractivity
