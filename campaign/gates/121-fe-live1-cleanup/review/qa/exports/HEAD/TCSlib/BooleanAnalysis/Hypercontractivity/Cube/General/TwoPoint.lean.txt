/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import TCSlib.BooleanAnalysis.Hypercontractivity.Cube.General.Duality

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Scalar bounds for general exponents

This is one stage of the forward hypercontractivity proof on the uniform Boolean cube.

## Main definitions

Shared definitions are imported; local technical helpers accompany their proofs.

## Main results

* `avg_rpow_ge_one`.
* `convex_sym_sum_mono`.
* `rpow_sum_antitone_exponent`.
* `h_alpha_ineq`.
* `integrated_h_alpha_ineq`.
* `rpow_ge_one_add_mul_sub`.
* `two_point_ineq_general_unit`.
* `low_norms_one_bit`.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014, §§9.3–10.1.
-/

open BooleanAnalysis MeasureTheory Set Filter ProbabilityTheory Real
open scoped BigOperators ENNReal Classical

namespace BooleanAnalysis.Hypercontractivity

variable {n : ℕ}

/-! ## General Two-Point Inequality (Unit Case)
The key real-analysis inequality needed for the (p, q) one-bit hypercontractivity.
-/
/-- The average M(b) = ((1+b)^p + (1-b)^p)/2 is at least 1 for b ∈ [0,1] and p ≥ 1.
**Source:** [OD14, §10.1 (two-point proof)]. -/
lemma avg_rpow_ge_one {p b : ℝ} (hp : 1 ≤ p) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    1 ≤ ((1 + b) ^ p + (1 - b) ^ p) / 2 := by
  have h_jensen : ConvexOn ℝ (Set.Ici 0) (fun x : ℝ => x ^ p) := convexOn_rpow (by linarith)
  have := h_jensen.2 (show 0 ≤ 1 + b by linarith) (show 0 ≤ 1 - b by linarith)
  convert @this (1 / 2) (1 / 2) (by norm_num) (by norm_num) (by norm_num) using 1 <;>
    norm_num <;> ring_nf
  norm_num

/-- Gives the convex symmetric-sum monotonicity used in the two-point argument.

**Source:** [OD14, §10.1 (two-point proof)]. -/
lemma convex_sym_sum_mono {f : ℝ → ℝ} (hf : ConvexOn ℝ (Set.Ici 0) f)
    {x y : ℝ} (hx0 : 0 ≤ x) (hxy : x ≤ y) (hy1 : y ≤ 1) :
    f (1 + x) + f (1 - x) ≤ f (1 + y) + f (1 - y) := by
  by_cases hxy' : x < y;
  · -- For 0 ≤ x < y ≤ 1, apply the secant_mono lemma with a = 1-y, x = 1-x, y = 1+y.
    have h1 : (f (1 - x) - f (1 - y)) / (y - x) ≤ (f (1 + y) - f (1 - y)) / (2 * y) := by
      convert hf.secant_mono _ _ _ _ _ using 1 <;> norm_num;
      rotate_left;
      exact 1 - y;
      exact 1 - x;
      exact 1 + y;
      exacts [ by linarith, by linarith, by linarith, by linarith, by linarith, by rw [ show 1 - x - ( 1 - y ) = y - x by ring, show 1 + y - ( 1 - y ) = 2 * y by ring ] ; exact ⟨ fun h => fun _ => h, fun h => h ( by linarith ) ⟩ ];
    have := hf.slope_mono_adjacent ( show 0 ≤ 1 - y by linarith ) ( show 0 ≤ 1 + y by linarith ) ( show 1 - y < 1 + x by linarith ) ( show 1 + x < 1 + y by linarith ) ; norm_num at * ; rw [ div_le_div_iff₀ ] at * <;> nlinarith;
  · rw [ le_antisymm hxy ( not_lt.mp hxy' ) ]


/-- Shows antitonicity in the exponent for the symmetric real-power sum.

**Source:** [OD14, §10.1 (two-point proof)]. -/
lemma rpow_sum_antitone_exponent {p q : ℝ} {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) (_hp0 : p ≤ 0) (hpq : p ≤ q) (hq0 : q ≤ 0) :
    (1 + x) ^ p + (1 - x) ^ p ≥ (1 + x) ^ q + (1 - x) ^ q := by
  by_contra! h_contra;
  -- Let's define the function \( f(t) = (1 + x)^t + (1 - x)^t \) and show that its derivative is non-positive on \((-\infty, 0]\).
  set f : ℝ → ℝ := fun t => (1 + x)^t + (1 - x)^t
  have hf_deriv_nonpos : ∀ t < 0, deriv f t ≤ 0 := by
    intro t ht; norm_num [ f, Real.rpow_def_of_pos ( by linarith : 0 < 1 + x ), Real.rpow_def_of_pos ( by linarith : 0 < 1 - x ), mul_comm ];
    -- Since $t < 0$, we have $t * \log(1 + x) < 0$ and $t * \log(1 - x) > 0$.
    have h_exp_neg : Real.exp (t * Real.log (1 + x)) ≤ 1 ∧ Real.exp (t * Real.log (1 - x)) ≥ 1 := by
      exact ⟨ Real.exp_le_one_iff.mpr ( mul_nonpos_of_nonpos_of_nonneg ht.le ( Real.log_nonneg ( by linarith ) ) ), Real.one_le_exp ( mul_nonneg_of_nonpos_of_nonpos ht.le ( Real.log_nonpos ( by linarith ) ( by linarith ) ) ) ⟩;
    nlinarith [ Real.log_le_sub_one_of_pos ( by linarith : 0 < 1 + x ), Real.log_le_sub_one_of_pos ( by linarith : 0 < 1 - x ), Real.exp_pos ( t * Real.log ( 1 + x ) ), Real.exp_pos ( t * Real.log ( 1 - x ) ) ];
  -- Since $f$ is differentiable and its derivative is non-positive on $(-\infty, 0]$, we can apply the Mean Value Theorem to $f$ on the interval $[p, q]$.
  have h_mvt : ∃ c ∈ Set.Ioo p q, deriv f c = (f q - f p) / (q - p) := by
    apply_rules [ exists_deriv_eq_slope ];
    · exact hpq.lt_of_ne ( by rintro rfl; linarith );
    · exact continuousOn_of_forall_continuousAt fun t ht => ContinuousAt.add ( ContinuousAt.rpow continuousAt_const continuousAt_id <| Or.inl <| by linarith ) ( ContinuousAt.rpow continuousAt_const continuousAt_id <| Or.inl <| by linarith );
    · exact DifferentiableOn.add ( DifferentiableOn.rpow ( differentiableOn_const _ ) differentiableOn_id ( by intro t ht; linarith ) ) ( DifferentiableOn.rpow ( differentiableOn_const _ ) differentiableOn_id ( by intro t ht; linarith ) );
  obtain ⟨ c, ⟨ hpc, hcq ⟩, hcd ⟩ := h_mvt; have := hf_deriv_nonpos c ( by linarith ) ; rw [ hcd, div_le_iff₀ ] at this <;> linarith;


/-- Establishes the auxiliary inequality used to compare interpolation parameters.

**Source:** [OD14, §10.1 (two-point proof)].

**Proof sketch.** Handle r = 0 directly; otherwise differentiate the difference of the two
sides. The identity c²s = r reduces derivative nonnegativity to comparison of symmetric sums
with nonpositive exponents, using their monotonicity in the exponent and displacement from one.
The difference vanishes at zero, so the mean value theorem proves the bound.
-/
lemma h_alpha_ineq {r s c t : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) (hs : s ≤ 1)
    (hc : c = Real.sqrt (r / s)) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 + t) ^ r - (1 - t) ^ r ≥ c * ((1 + c * t) ^ s - (1 - c * t) ^ s) := by
  by_cases hr0 : r = 0;
  · aesop;
  · -- Let's define the function $g(t)$ and show that its derivative is non-negative on $(0,1)$.
    set g : ℝ → ℝ := fun t => (1 + t)^r - (1 - t)^r - c * ((1 + c * t)^s - (1 - c * t)^s)
    have hg_deriv_nonneg : ∀ t ∈ Set.Ioo 0 1, 0 ≤ deriv g t := by
      -- Let's simplify the expression for the derivative.
      have h_deriv_simplified : ∀ t ∈ Set.Ioo 0 1, deriv g t = r * ((1 + t)^(r - 1) + (1 - t)^(r - 1) - (c^2 * s / r) * ((1 + c * t)^(s - 1) + (1 - c * t)^(s - 1))) := by
        intro t ht;
        convert HasDerivAt.deriv ( HasDerivAt.sub ( HasDerivAt.sub ( HasDerivAt.rpow_const ( hasDerivAt_id' t |> HasDerivAt.const_add _ ) _ ) ( HasDerivAt.rpow_const ( hasDerivAt_id' t |> HasDerivAt.const_sub _ ) _ ) ) ( HasDerivAt.const_mul c ( HasDerivAt.sub ( HasDerivAt.rpow_const ( HasDerivAt.const_add _ ( hasDerivAt_id' t |> HasDerivAt.const_mul _ ) ) _ ) ( HasDerivAt.rpow_const ( HasDerivAt.const_sub _ ( hasDerivAt_id' t |> HasDerivAt.const_mul _ ) ) _ ) ) ) ) using 1 <;> norm_num;
        · grind;
        · exact Or.inl <| by linarith [ ht.1 ] ;
        · exact Or.inl <| by linarith [ ht.1, ht.2 ] ;
        · exact Or.inl ( by nlinarith [ ht.1, ht.2, show 0 ≤ c by rw [ hc ] ; positivity ] );
        · exact Or.inl ( by nlinarith [ ht.1, ht.2, show c ≤ 1 by rw [ hc ] ; exact Real.sqrt_le_iff.mpr ⟨ by positivity, by rw [ div_le_iff₀ ] <;> linarith [ show 0 < r by positivity ] ⟩ ] );
      -- Since $c^2 * s / r = 1$, we can simplify the expression for the derivative.
      have h_deriv_simplified' : ∀ t ∈ Set.Ioo 0 1, deriv g t = r * ((1 + t)^(r - 1) + (1 - t)^(r - 1) - ((1 + c * t)^(s - 1) + (1 - c * t)^(s - 1))) := by
        intro t ht; rw [ h_deriv_simplified t ht ] ; rw [ hc ] ; rw [ Real.sq_sqrt <| div_nonneg hr <| by linarith ] ; ring_nf;
        grind +splitImp;
      -- Since $r \leq s$, we have $(1 + t)^{r-1} + (1 - t)^{r-1} \geq (1 + c * t)^{s-1} + (1 - c * t)^{s-1}$ for $t \in (0, 1)$.
      have h_ineq : ∀ t ∈ Set.Ioo 0 1, (1 + t)^(r - 1) + (1 - t)^(r - 1) ≥ (1 + c * t)^(s - 1) + (1 - c * t)^(s - 1) := by
        intros t ht
        have h_ineq_step1 : (1 + t)^(r - 1) + (1 - t)^(r - 1) ≥ (1 + t)^(s - 1) + (1 - t)^(s - 1) := by
          exact rpow_sum_antitone_exponent ht.1 ht.2 ( by linarith ) ( by linarith ) ( by linarith );
        have h_ineq_step2 : (1 + t)^(s - 1) + (1 - t)^(s - 1) ≥ (1 + c * t)^(s - 1) + (1 - c * t)^(s - 1) := by
          have h_deriv_nonneg : ∀ x ∈ Set.Ioo 0 t, deriv (fun x => (1 + x)^(s - 1) + (1 - x)^(s - 1)) x ≥ 0 := by
            intros x hx
            have h_deriv : deriv (fun x => (1 + x)^(s - 1) + (1 - x)^(s - 1)) x = (s - 1) * ((1 + x)^(s - 2) - (1 - x)^(s - 2)) := by
              convert HasDerivAt.deriv ( HasDerivAt.add ( HasDerivAt.rpow_const ( hasDerivAt_id' x |> HasDerivAt.const_add _ ) _ ) ( HasDerivAt.rpow_const ( hasDerivAt_id' x |> HasDerivAt.const_sub _ ) _ ) ) using 1 <;> norm_num <;> ring_nf;
              · exact Or.inl <| by linarith [ hx.1 ] ;
              · exact Or.inl <| by linarith [ hx.1, hx.2, ht.1, ht.2 ] ;
            exact h_deriv.symm ▸ mul_nonneg_of_nonpos_of_nonpos ( by linarith ) ( sub_nonpos_of_le ( by rw [ Real.rpow_le_rpow_iff_of_neg ] <;> linarith [ hx.1, hx.2, ht.1, ht.2 ] ) )
          by_cases h_cases : c * t < t;
          · have := exists_deriv_eq_slope ( f := fun x => ( 1 + x ) ^ ( s - 1 ) + ( 1 - x ) ^ ( s - 1 ) ) h_cases;
            contrapose! this;
            simp +zetaDelta at *;
            refine' ⟨ _, _, _ ⟩;
            · exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.add ( ContinuousAt.rpow ( continuousAt_const.add continuousAt_id ) continuousAt_const <| Or.inl <| by linarith [ hx.1, show 0 ≤ c * t by exact mul_nonneg ( hc.symm ▸ Real.sqrt_nonneg _ ) ht.1.le ] ) ( ContinuousAt.rpow ( continuousAt_const.sub continuousAt_id ) continuousAt_const <| Or.inl <| by linarith [ hx.2, show c * t < t by linarith ] );
            · exact DifferentiableOn.add ( DifferentiableOn.rpow ( differentiableOn_id.const_add _ ) ( differentiableOn_const _ ) ( by intro x hx; linarith [ hx.1, hx.2, show 0 ≤ c * t by exact mul_nonneg ( hc.symm ▸ Real.sqrt_nonneg _ ) ht.1.le ] ) ) ( DifferentiableOn.rpow ( differentiableOn_id.const_sub _ ) ( differentiableOn_const _ ) ( by intro x hx; linarith [ hx.1, hx.2, show 0 ≤ c * t by exact mul_nonneg ( hc.symm ▸ Real.sqrt_nonneg _ ) ht.1.le ] ) );
            · intro x hx₁ hx₂; rw [ eq_div_iff ] <;> nlinarith [ h_deriv_nonneg x ( by nlinarith [ show 0 ≤ c by rw [ hc ] ; positivity ] ) hx₂ ] ;
          · norm_num [ show c = 1 by nlinarith [ ht.1, ht.2, show 0 ≤ c by rw [ hc ] ; positivity, show c ≤ 1 by rw [ hc ] ; exact Real.sqrt_le_iff.mpr ⟨ by positivity, by rw [ div_le_iff₀ ] <;> linarith [ show 0 < s by exact lt_of_lt_of_le ( lt_of_le_of_ne hr ( Ne.symm hr0 ) ) hrs ] ⟩ ] ] at *;
        linarith;
      exact fun t ht => h_deriv_simplified' t ht ▸ mul_nonneg hr ( sub_nonneg_of_le ( h_ineq t ht ) );
    by_contra h_contra;
    -- Apply the mean value theorem to the interval $[0, t]$.
    obtain ⟨ξ, hξ⟩ : ∃ ξ ∈ Set.Ioo 0 t, deriv g ξ = (g t - g 0) / (t - 0) := by
      apply_rules [ exists_deriv_eq_slope ];
      · exact ht0.lt_of_ne ( by rintro rfl; norm_num [ hr0 ] at h_contra );
      · refine' ContinuousOn.sub _ _;
        · exact continuousOn_of_forall_continuousAt fun x hx => by exact ContinuousAt.sub ( ContinuousAt.rpow ( continuousAt_const.add continuousAt_id ) continuousAt_const <| Or.inr <| by positivity ) ( ContinuousAt.rpow ( continuousAt_const.sub continuousAt_id ) continuousAt_const <| Or.inr <| by positivity ) ;
        · refine' ContinuousOn.mul continuousOn_const _;
          refine' ContinuousOn.sub _ _;
          · exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.rpow ( continuousAt_const.add ( continuousAt_const.mul continuousAt_id ) ) continuousAt_const <| Or.inr <| by linarith [ show 0 < s by exact lt_of_lt_of_le ( by positivity ) hrs ] ;
          · exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.rpow ( continuousAt_const.sub ( continuousAt_const.mul continuousAt_id ) ) continuousAt_const <| Or.inr <| by linarith [ show 0 < s by exact lt_of_lt_of_le ( by positivity ) hrs ] ;
      · refine' DifferentiableOn.sub _ _;
        · exact DifferentiableOn.sub ( DifferentiableOn.rpow ( differentiableOn_id.const_add _ ) ( differentiableOn_const _ ) ( by intro x hx; linarith [ hx.1 ] ) ) ( DifferentiableOn.rpow ( differentiableOn_id.const_sub _ ) ( differentiableOn_const _ ) ( by intro x hx; linarith [ hx.2 ] ) );
        · refine' DifferentiableOn.mul _ _;
          · exact differentiableOn_const _;
          · refine' DifferentiableOn.sub _ _;
            · exact DifferentiableOn.rpow ( DifferentiableOn.add ( differentiableOn_const _ ) ( differentiableOn_id.const_mul _ ) ) ( differentiableOn_const _ ) ( by intro x hx; exact ne_of_gt ( add_pos_of_pos_of_nonneg zero_lt_one ( mul_nonneg ( hc.symm ▸ Real.sqrt_nonneg _ ) hx.1.le ) ) );
            · exact DifferentiableOn.rpow ( DifferentiableOn.sub ( differentiableOn_const _ ) ( differentiableOn_id.const_mul _ ) ) ( differentiableOn_const _ ) ( by intro x hx; exact ne_of_gt ( sub_pos.mpr ( by nlinarith [ hx.1, hx.2, show c ≤ 1 by rw [ hc ] ; exact Real.sqrt_le_iff.mpr ⟨ by positivity, by rw [ div_le_iff₀ ] <;> linarith [ show 0 < r by positivity ] ⟩ ] ) ) );
    simp +zetaDelta at *;
    rw [ eq_div_iff ] at hξ <;> nlinarith [ hg_deriv_nonneg ξ hξ.1.1 ( by linarith ) ]

/-
The integrated form of h_alpha_ineq via MVT.
From h_alpha_ineq we know that for 0 ≤ r ≤ s ≤ 1, c = √(r/s), 0 ≤ t ≤ 1:
  (1+t)^r - (1-t)^r ≥ c * ((1+ct)^s - (1-ct)^s)
Integrating (via MVT) from 0 to b gives:
  ((1+b)^(r+1) + (1-b)^(r+1) - 2)/(r+1) ≥ ((1+cb)^(s+1) + (1-cb)^(s+1) - 2)/(s+1)
-/
/-- Integrates the auxiliary two-point inequality over a one-bit parameter.

**Source:** [OD14, §10.1 (two-point proof)].

**Proof sketch.** Differentiate the difference of the normalized symmetric-power expressions.
The auxiliary bound with exponents p − 1 and q − 1 makes its derivative nonnegative, and it
vanishes at zero. Continuity and the mean value theorem include the endpoint b = 1.
-/
lemma integrated_h_alpha_ineq {p q b : ℝ} (hp1 : 1 ≤ p) (hpq : p ≤ q) (hq2 : q ≤ 2)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    let ρ := Real.sqrt ((p - 1) / (q - 1))
    ((1 + ρ * b) ^ q + (1 - ρ * b) ^ q - 2) / q ≤
    ((1 + b) ^ p + (1 - b) ^ p - 2) / p := by
      -- Define the function g(t) and show that its derivative is non-negative.
      set ρ := Real.sqrt ((p - 1) / (q - 1))
      set g : ℝ → ℝ := fun t => ((1 + t) ^ p + (1 - t) ^ p - 2) / p - ((1 + ρ * t) ^ q + (1 - ρ * t) ^ q - 2) / q
      have hg_deriv_nonneg : ∀ t ∈ Set.Ioo 0 b, 0 ≤ deriv g t := by
        -- By definition of $g$, we can compute its derivative.
        have hg_deriv : ∀ t ∈ Set.Ioo 0 b, deriv g t = ((1 + t) ^ (p - 1) - (1 - t) ^ (p - 1)) - ρ * ((1 + ρ * t) ^ (q - 1) - (1 - ρ * t) ^ (q - 1)) := by
          intro t ht; refine' HasDerivAt.deriv _; convert HasDerivAt.sub ( HasDerivAt.div_const ( HasDerivAt.sub ( HasDerivAt.add
          ( HasDerivAt.rpow_const ( hasDerivAt_id' t |> HasDerivAt.const_add _ ) _ ) ( HasDerivAt.rpow_const ( hasDerivAt_id' t |>
          HasDerivAt.const_sub _ ) _ ) ) ( hasDerivAt_const _ _ ) ) _ ) ( HasDerivAt.div_const ( HasDerivAt.sub ( HasDerivAt.add ( HasDerivAt.rpow_const
          ( HasDerivAt.const_add _ ( HasDerivAt.const_mul _ ( hasDerivAt_id' t ) ) ) _ ) ( HasDerivAt.rpow_const ( HasDerivAt.const_sub _ ( HasDerivAt.const_mul _
          ( hasDerivAt_id' t ) ) ) _ ) ) ( hasDerivAt_const _ _ ) ) _ ) using 1 <;> norm_num [ show p ≠ 0 by linarith, show q ≠ 0 by linarith ] ; ring_nf;
          · simp +decide [ mul_assoc, mul_comm p, mul_left_comm q, ne_of_gt ( zero_lt_one.trans_le hp1 ), ne_of_gt ( zero_lt_one.trans_le ( by linarith : 1 ≤ q ) ) ];
          · exact Or.inl <| by linarith [ ht.1 ] ;
          · exact Or.inl <| by linarith [ ht.1, ht.2 ] ;
          · exact Or.inl <| by nlinarith [ ht.1, ht.2, Real.sqrt_nonneg ( ( p - 1 ) / ( q - 1 ) ) ] ;
          · exact Or.inr ( by linarith );
        have := @h_alpha_ineq;
        intro t ht; specialize this ( show 0 ≤ p - 1 by linarith ) ( show p - 1 ≤ q - 1 by linarith ) ( show q - 1 ≤ 1 by linarith ) rfl ( show 0 ≤ t by linarith [ ht.1 ] ) ( show t ≤ 1 by linarith [ ht.2 ] ) ; aesop;
      by_cases hb : b = 0;
      · norm_num [ hb ];
      · have := exists_deriv_eq_slope g ( show b > 0 from lt_of_le_of_ne hb0 ( Ne.symm hb ) );
        simp +zetaDelta at *;
        contrapose! this;
        refine' ⟨ _, _, _ ⟩;
        · refine' ContinuousOn.sub _ _;
          · exact continuousOn_of_forall_continuousAt fun t ht => ContinuousAt.div ( ContinuousAt.sub ( ContinuousAt.add ( ContinuousAt.rpow ( continuousAt_const.add continuousAt_id ) continuousAt_const <| Or.inr <| by linarith ) ( ContinuousAt.rpow ( continuousAt_const.sub continuousAt_id ) continuousAt_const <| Or.inr <| by linarith ) ) continuousAt_const ) continuousAt_const <| by linarith;
          · refine' ContinuousOn.div_const _ _;
            refine' ContinuousOn.sub _ continuousOn_const;
            exact ContinuousOn.add ( ContinuousOn.rpow ( continuousOn_const.add ( continuousOn_const.mul continuousOn_id ) ) continuousOn_const <| by intro t ht; exact Or.inr <| by linarith ) ( ContinuousOn.rpow ( continuousOn_const.sub ( continuousOn_const.mul continuousOn_id ) ) continuousOn_const <| by intro t ht; exact Or.inr <| by linarith );
        · refine' fun t ht => DifferentiableAt.differentiableWithinAt _;
          apply_rules [ DifferentiableAt.sub, DifferentiableAt.div, DifferentiableAt.add, DifferentiableAt.rpow_const ] <;> norm_num [ add_comm, mul_comm ];
          any_goals contrapose! hb; linarith;
          · exact differentiableAt_id.const_mul _;
          · exact differentiableAt_id.const_mul _;
        · intro c hc; rw [ ne_eq, eq_div_iff ] <;> norm_num <;> nlinarith [ hg_deriv_nonneg c hc.1 hc.2 ] ;

/-
Tangent line inequality for x^r at x = 1: for x ≥ 0, r ≥ 1, x^r ≥ 1 + r*(x-1).
-/
/-- Gives the real-power lower bound used in the two-point hypercontractive inequality.

**Source:** [OD14, §10.1 (two-point proof)]. -/
lemma rpow_ge_one_add_mul_sub {x r : ℝ} (hx : 0 ≤ x) (hr : 1 ≤ r) :
    x ^ r ≥ 1 + r * (x - 1) := by
      have := @Real.geom_mean_le_arith_mean;
      specialize this { 0, 1 } ( fun i => if i = 0 then 1 else r - 1 ) ( fun i => if i = 0 then x ^ r else 1 ) ; norm_num at *;
      specialize this hr ( by positivity ) ( by positivity ) ; rw [ ← Real.rpow_mul ( by positivity ), mul_inv_cancel₀ ( by positivity ), Real.rpow_one ] at this ; rw [ le_div_iff₀ ( by positivity ) ] at this ; nlinarith;

/-
The general two-point inequality in the unit case.
Proved using integrated_h_alpha_ineq and rpow_ge_one_add_mul_sub,
without circular dependence on low_norms_hypercontractivity.
-/
/-- Proves the normalized two-point inequality for arbitrary exponents between one and two.

**Source:** [OD14, §10.1 (two-point proof)]. -/
theorem two_point_ineq_general_unit (b p q : ℝ) (hp1 : 1 ≤ p) (hpq : p ≤ q) (hq2 : q ≤ 2)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    let ρ := Real.sqrt ((p - 1) / (q - 1))
    ((1 + ρ * b) ^ q + (1 - ρ * b) ^ q) / 2 ≤
    (((1 + b) ^ p + (1 - b) ^ p) / 2) ^ (q / p) := by
      by_cases hq : q = 0 <;> by_cases hp : p = 0 <;> simp_all +decide [ mul_comm, div_eq_mul_inv ];
      · norm_num at *;
      · linarith;
      · linarith;
      · have := @integrated_h_alpha_ineq p q b hp1 hpq hq2 hb0 hb1;
        have := @rpow_ge_one_add_mul_sub ( ( ( 1 + b ) ^ p + ( 1 - b ) ^ p ) / 2 ) ( q / p ) ?_ ?_ <;> norm_num at *;
        · field_simp at *;
          rw [ div_le_iff₀ ( by linarith ) ] at this;
          rw [ Real.sqrt_div ( by linarith ) ] at * ; ring_nf at * ; nlinarith [ mul_inv_cancel_left₀ hp q ] ;
        · exact div_nonneg ( add_nonneg ( Real.rpow_nonneg ( by linarith ) _ ) ( Real.rpow_nonneg ( by linarith ) _ ) ) zero_le_two;
        · rw [ le_div_iff₀ ] <;> linarith

/-! ## One-Bit Low Norms Hypercontractivity -/
/-
One-bit (p, q)-hypercontractivity for 1 < p ≤ q ≤ 2.
Uses the general two-point inequality applied to the Fourier coefficients.
This is proved WITHOUT using general_one_function_hypercontractivity (to avoid circularity).
-/
/-- Establishes the one-bit hypercontractive estimate in the low-exponent regime.

**Source:** [OD14, §10.1].

**Proof sketch.** Express the function and its noisy version using their two Fourier
coefficients, and make both coefficients nonnegative by sign symmetries. Normalize by the
constant coefficient when it is larger and apply the unit inequality. Otherwise, exchanging the
coefficients increases the noisy absolute values and preserves the input moment. Rescale by
homogeneity.
-/
theorem low_norms_one_bit (p q : ℝ) (hp : 1 < p) (hpq : p ≤ q) (hq : q ≤ 2)
    (f : BooleanFunc 1) :
    (expect (fun x => |noiseOp (Real.sqrt ((p - 1) / (q - 1))) f x| ^ q)) ^ (1 / q) ≤
    (expect (fun x => |f x| ^ p)) ^ (1 / p) := by
  -- Use the one-bit structure directly with two_point_ineq_general_unit
  set a := fourierCoeff f ∅
  set b := fourierCoeff f {⟨0, by omega⟩}
  set ρ := Real.sqrt ((p - 1) / (q - 1))
  -- Rewrite the Lp norm of f
  rw [expect_abs_rpow_one_bit p f]
  -- For the noise-operated function, we need its Lq norm
  -- The noise operator on one-bit functions: noiseOp ρ f has values a+ρb and a-ρb
  rw [expect_abs_rpow_one_bit q (noiseOp ρ f)]
  -- Now the goal involves Fourier coefficients of noiseOp ρ f
  -- fourierCoeff (noiseOp ρ f) ∅ = a and fourierCoeff (noiseOp ρ f) {0} = ρ * b
  -- After simplification, the goal becomes:
  -- ((|a + ρb|^q + |a - ρb|^q)/2)^{1/q} ≤ ((|a + b|^p + |a - b|^p)/2)^{1/p}
  -- This is the general two-point inequality
  -- Apply the general two-point inequality to the Fourier coefficients.
  have h_two_point : ((|a + ρ * b| ^ q + |a - ρ * b| ^ q) / 2) ^ (1 / q) ≤ ((|a + b| ^ p + |a - b| ^ p) / 2) ^ (1 / p) := by
    -- Without loss of generality, assume $b \geq 0$.
    suffices h_wlog : ∀ {a b : ℝ}, 0 ≤ b → ((|a + ρ * b| ^ q + |a - ρ * b| ^ q) / 2) ^ (1 / q) ≤ ((|a + b| ^ p + |a - b| ^ p) / 2) ^ (1 / p) by
      cases le_total 0 b <;> simp_all +decide ;
      convert @h_wlog a ( -b ) ( by linarith ) using 1 <;> norm_num [ abs_sub_comm ];
      · ring_nf;
      · ring_nf;
    intro a b hb_nonneg
    suffices h_wlog : ∀ {a b : ℝ}, 0 ≤ b → 0 ≤ a → ((|a + ρ * b| ^ q + |a - ρ * b| ^ q) / 2) ^ (1 / q) ≤ ((|a + b| ^ p + |a - b| ^ p) / 2) ^ (1 / p) by
      cases abs_cases a <;> simp +decide [ * ];
      · simpa using h_wlog hb_nonneg ( by linarith );
      · convert h_wlog hb_nonneg ( neg_nonneg.mpr ( by linarith : a ≤ 0 ) ) using 1 <;> norm_num [ abs_sub_comm ];
        · rw [ show -a + ρ * b = - ( a - ρ * b ) by ring, show -a - ρ * b = - ( a + ρ * b ) by ring, abs_neg, abs_neg ] ; ring_nf;
        · congr 1; congr 1; rw [show |-a + b| = |a - b| from by rw [show -a + b = -(a - b) from by ring, abs_neg]]; rw [add_comm]; rw [show |a + b| = |b + a| from by rw [add_comm]]
    intro a b hb_nonneg ha_nonneg
    by_cases hab : a ≥ b;
    · by_cases ha : a = 0;
      · simp_all +decide [ show b = 0 by linarith ];
        norm_num [ show q ≠ 0 by linarith, show p ≠ 0 by linarith ];
      · -- Let $t = \frac{b}{a}$, then $0 \leq t \leq 1$.
        set t := b / a
        have ht : 0 ≤ t ∧ t ≤ 1 := by
          exact ⟨ div_nonneg hb_nonneg ha_nonneg, div_le_one_of_le₀ hab ha_nonneg ⟩;
        -- Apply the general two-point inequality to $t$.
        have h_two_point : ((|1 + ρ * t| ^ q + |1 - ρ * t| ^ q) / 2) ^ (1 / q) ≤ ((|1 + t| ^ p + |1 - t| ^ p) / 2) ^ (1 / p) := by
          have := @two_point_ineq_general_unit;
          convert Real.rpow_le_rpow _ ( this t p q hp.le hpq hq ht.1 ht.2 ) ( show 0 ≤ 1 / q by exact one_div_nonneg.mpr ( by linarith ) ) using 1;
          · rw [ abs_of_nonneg, abs_of_nonneg ] <;> norm_num;
            · exact le_trans ( mul_le_of_le_one_right ( Real.sqrt_nonneg _ ) ht.2 ) ( Real.sqrt_le_iff.mpr ⟨ by positivity, by rw [ div_le_iff₀ ] <;> nlinarith ⟩ );
            · exact add_nonneg zero_le_one ( mul_nonneg ( Real.sqrt_nonneg _ ) ht.1 );
          · rw [ ← Real.rpow_mul ( by exact div_nonneg ( add_nonneg ( Real.rpow_nonneg ( by linarith ) _ ) ( Real.rpow_nonneg ( by linarith ) _ ) ) zero_le_two ), mul_comm ] ; ring_nf ; norm_num [ show p ≠ 0 by linarith, show q ≠ 0 by linarith ];
            rw [ abs_of_nonneg ( by linarith ), abs_of_nonneg ( by linarith ) ];
          · exact div_nonneg ( add_nonneg ( Real.rpow_nonneg ( by nlinarith [ Real.sqrt_nonneg ( ( p - 1 ) / ( q - 1 ) ) ] ) _ ) ( Real.rpow_nonneg ( by nlinarith [ Real.sqrt_nonneg ( ( p - 1 ) / ( q - 1 ) ), show Real.sqrt ( ( p - 1 ) / ( q - 1 ) ) * t ≤ 1 by exact mul_le_one₀ ( Real.sqrt_le_iff.mpr ⟨ by positivity, by rw [ div_le_iff₀ ] <;> linarith ⟩ ) ht.1 ht.2 ] ) _ ) ) zero_le_two;
        convert mul_le_mul_of_nonneg_left h_two_point ( show 0 ≤ |a| by positivity ) using 1 <;> norm_num [ abs_div, abs_mul, abs_of_nonneg, ha_nonneg, hb_nonneg, ha ];
        · rw [ show a + ρ * b = a * ( 1 + ρ * t ) by rw [ mul_add, mul_left_comm, mul_div_cancel₀ _ ha ] ; ring, show a - ρ * b = a * ( 1 - ρ * t ) by rw [ mul_sub, mul_left_comm, mul_div_cancel₀ _ ha ] ; ring, abs_mul, abs_mul, abs_of_nonneg ha_nonneg ] ; ring_nf;
          rw [ Real.mul_rpow ( by positivity ) ( by positivity ), Real.mul_rpow ( by positivity ) ( by positivity ) ] ; ring_nf;
          rw [ show a ^ q * |1 + ρ * t| ^ q * ( 1 / 2 ) + a ^ q * |1 - ρ * t| ^ q * ( 1 / 2 ) = a ^ q * ( |1 + ρ * t| ^ q * ( 1 / 2 ) + |1 - ρ * t| ^ q * ( 1 / 2 ) ) by ring, Real.mul_rpow ( by positivity ) ( by positivity ), ← Real.rpow_mul ( by positivity ), mul_inv_cancel₀ ( by linarith ), Real.rpow_one ];
        · rw [ show a + b = a * ( 1 + t ) by rw [ mul_add, mul_div_cancel₀ _ ha ] ; ring, show a - b = a * ( 1 - t ) by rw [ mul_sub, mul_div_cancel₀ _ ha ] ; ring, abs_mul, abs_mul, abs_of_nonneg ha_nonneg ];
          rw [ Real.mul_rpow ( by positivity ) ( by positivity ), Real.mul_rpow ( by positivity ) ( by positivity ) ];
          rw [ show ( a ^ p * |1 + t| ^ p + a ^ p * |1 - t| ^ p ) / 2 = a ^ p * ( ( |1 + t| ^ p + |1 - t| ^ p ) / 2 ) by ring, Real.mul_rpow ( by positivity ) ( by positivity ), ← Real.rpow_mul ( by positivity ), mul_inv_cancel₀ ( by positivity ), Real.rpow_one ];
    · -- Since $a < b$, we have $|a + \rho b| \leq |b + \rho a|$ and $|a - \rho b| \leq |b - \rho a|$.
      have h_abs : |a + ρ * b| ≤ |b + ρ * a| ∧ |a - ρ * b| ≤ |b - ρ * a| := by
        constructor <;> rw [ abs_le ] <;> constructor <;> cases abs_cases ( b + ρ * a ) <;> cases abs_cases ( b - ρ * a ) <;> nlinarith [ show 0 ≤ ρ by positivity, show ρ ≤ 1 by exact Real.sqrt_le_iff.mpr ⟨ by positivity, by rw [ div_le_iff₀ ] <;> linarith ⟩ ];
      have h_abs_pow : |a + ρ * b| ^ q + |a - ρ * b| ^ q ≤ |b + ρ * a| ^ q + |b - ρ * a| ^ q := by
        exact add_le_add ( Real.rpow_le_rpow ( abs_nonneg _ ) h_abs.1 ( by linarith ) ) ( Real.rpow_le_rpow ( abs_nonneg _ ) h_abs.2 ( by linarith ) );
      have h_abs_pow : ((|b + ρ * a| ^ q + |b - ρ * a| ^ q) / 2) ^ (1 / q) ≤ ((|b + a| ^ p + |b - a| ^ p) / 2) ^ (1 / p) := by
        have := @two_point_ineq_general_unit;
        specialize this ( a / b ) p q ( by linarith ) ( by linarith ) ( by linarith ) ( by positivity ) ( by rw [ div_le_iff₀ ( by linarith ) ] ; linarith );
        by_cases hb : b = 0 <;> simp_all +decide;
        convert Real.rpow_le_rpow ( by positivity ) ( show ( ( |b + ρ * a| ^ q + |b - ρ * a| ^ q ) / 2 ) ≤ ( ( |b + a| ^ p + |b - a| ^ p ) / 2 ) ^ ( q / p ) from ?_ ) ( show 0 ≤ q⁻¹ by exact inv_nonneg.mpr ( by linarith ) ) using 1;
        · rw [ ← Real.rpow_mul ( by positivity ) ] ; ring_nf ; norm_num [ show q ≠ 0 by linarith ];
        · convert mul_le_mul_of_nonneg_left this ( show 0 ≤ b ^ q by positivity ) using 1 <;> ring_nf;
          · rw [ show b + ρ * a = b * ( 1 + a * ρ * b⁻¹ ) by nlinarith [ mul_inv_cancel_left₀ hb ( a * ρ ) ], show b - ρ * a = b * ( 1 - a * ρ * b⁻¹ ) by nlinarith [ mul_inv_cancel_left₀ hb ( a * ρ ) ], abs_of_nonneg ( by positivity ), abs_of_nonneg ( by nlinarith [ mul_inv_cancel_left₀ hb ( a * ρ ), show ρ ≤ 1 by exact Real.sqrt_le_iff.mpr ⟨ by positivity, by rw [ div_le_iff₀ ] <;> nlinarith ⟩ ] ) ] ; rw [ Real.mul_rpow ( by positivity ) ( by positivity ), Real.mul_rpow ( by positivity ) ( by nlinarith [ mul_inv_cancel_left₀ hb ( a * ρ ), show ρ ≤ 1 by exact Real.sqrt_le_iff.mpr ⟨ by positivity, by rw [ div_le_iff₀ ] <;> nlinarith ⟩ ] ) ] ; ring_nf;
            grind;
          · rw [ show |b + a| = b + a by rw [ abs_of_nonneg ] ; linarith, show |b - a| = b - a by rw [ abs_of_nonneg ] ; linarith ] ; ring_nf;
            rw [ show b + a = b * ( 1 + a / b ) by rw [ mul_add, mul_div_cancel₀ _ hb ] ; ring, show b - a = b * ( 1 - a / b ) by rw [ mul_sub, mul_div_cancel₀ _ hb ] ; ring, Real.mul_rpow ( by positivity ) ( by positivity ), Real.mul_rpow ( by positivity ) ( by exact sub_nonneg.mpr <| div_le_one_of_le₀ ( by linarith ) <| by positivity ) ] ; ring_nf;
            rw [ show b ^ p * ( 1 + a * b⁻¹ ) ^ p * ( 1 / 2 ) + b ^ p * ( 1 - a * b⁻¹ ) ^ p * ( 1 / 2 ) = b ^ p * ( ( 1 + a * b⁻¹ ) ^ p * ( 1 / 2 ) + ( 1 - a * b⁻¹ ) ^ p * ( 1 / 2 ) ) by ring, Real.mul_rpow ( by positivity ) ( by exact add_nonneg ( mul_nonneg ( Real.rpow_nonneg ( by nlinarith [ mul_inv_cancel₀ hb ] ) _ ) ( by positivity ) ) ( mul_nonneg ( Real.rpow_nonneg ( by nlinarith [ mul_inv_cancel₀ hb ] ) _ ) ( by positivity ) ) ), ← Real.rpow_mul ( by positivity ), mul_comm ] ; ring_nf;
            norm_num [ show p ≠ 0 by linarith ];
      simp_all +decide [ add_comm, abs_sub_comm ];
      exact le_trans ( Real.rpow_le_rpow ( by positivity ) ( by linarith ) ( by exact inv_nonneg.mpr ( by linarith ) ) ) h_abs_pow;
  convert h_two_point using 3;
  unfold noiseOp; norm_num;
  unfold a b; unfold BooleanAnalysis.fourierCoeff; norm_num [ Finset.sum_range_succ, chiS ] ;
  unfold innerProduct;
  unfold expect; norm_num [ Finset.sum_range_succ, chiS ] ;
  unfold uniformWeight; norm_num [ Finset.sum_range_succ, chiS ] ;
  rw [ show ( Finset.univ : Finset ( Finset ( Fin 1 ) ) ) = { ∅, { 0 } } by decide ] ; simp +decide [Finset.prod_singleton, boolToSign ] ; ring_nf;
  rw [ show ( Finset.univ : Finset ( BoolCube 1 ) ) = { fun _ => Bool.true, fun _ => Bool.false } by decide ] ; simp +decide [Finset.sum_singleton ] ; ring_nf;
-- NEEDS: non-circular proof of two-point inequality for general (a, b, p, q, ρ)

end BooleanAnalysis.Hypercontractivity
