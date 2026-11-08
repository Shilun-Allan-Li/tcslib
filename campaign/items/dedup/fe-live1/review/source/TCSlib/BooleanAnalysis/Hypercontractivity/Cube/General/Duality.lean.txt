/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import TCSlib.BooleanAnalysis.Hypercontractivity.Cube.General.Tensorization

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Cube noise contraction and duality

This is one stage of the forward hypercontractivity proof on the uniform Boolean cube.

## Main definitions

Shared definitions are imported; local technical helpers accompany their proofs.

## Main results

* `noiseKernel_sum_right`.
* `noiseKernel_sum_left`.
* `noiseOp_abs_rpow_le_kernel_avg`.
* `trivial_contractivity`.
* `noise_op_norm_dual`.
* `Interpolation.sqrt_div_le_one`.
* `bridging_hypercontractivity`.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014, §§9.3–10.1.
-/

open BooleanAnalysis MeasureTheory Set Filter ProbabilityTheory Real
open scoped BigOperators ENNReal Classical

namespace BooleanAnalysis.Hypercontractivity

variable {n : ℕ}

/--
The noise kernel sums to 1 over the second argument.
**Source:** [OD14, Rem. 9.20 (proof)]. -/

lemma noiseKernel_sum_right {ρ : ℝ} (_hρ0 : 0 ≤ ρ) (_hρ1 : ρ ≤ 1)
    (x : BoolCube n) : ∑ y : BoolCube n, noiseKernel ρ x y = 1 := by
  unfold noiseKernel;
  -- The sum over y factorizes as a product of independent sums over each bit.
  have h_factor : ∑ y : BoolCube n, (∏ i : Fin n, (1 + ρ * boolToSign (x i) * boolToSign (y i)) / 2) = ∏ i : Fin n, ∑ y : Bool, (1 + ρ * boolToSign (x i) * boolToSign y) / 2 := by
    exact Eq.symm (Fintype.prod_sum fun i j => (1 + ρ * boolToSign (x i) * boolToSign j) / 2);
  rw [ h_factor, Finset.prod_eq_one ] ; intros ; norm_num [ Finset.sum_div _ _ _, boolToSign ] ; ring

/-
The noise kernel sums to 1 over the first argument (doubly stochastic).
-/
/-- Shows that the noise kernel has total mass one in its left argument.

**Source:** [OD14, Rem. 9.20 (proof)]. -/
lemma noiseKernel_sum_left {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (y : BoolCube n) : ∑ x : BoolCube n, noiseKernel ρ x y = 1 := by
  convert noiseKernel_sum_right hρ0 hρ1 y using 1;
  unfold noiseKernel; congr; ext; ring_nf;
  ac_rfl

/-
Jensen's inequality applied to the noise kernel: for convex `|·|^s` with `s ≥ 1`,
`|T_ρ f(x)|^s ≤ ∑_y K_ρ(x,y) |f(y)|^s`.
-/
/-- Bounds a noisy absolute-power moment by its kernel average.

**Source:** [OD14, Prop. 10.4 (proof)]. -/
lemma noiseOp_abs_rpow_le_kernel_avg {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (s : ℝ) (hs : 1 ≤ s) (f : BooleanFunc n) (x : BoolCube n) :
    |noiseOp ρ f x| ^ s ≤ ∑ y : BoolCube n, noiseKernel ρ x y * |f y| ^ s := by
  have h_triangle : |noiseOp ρ f x| ≤ ∑ y : BoolCube n, noiseKernel ρ x y * |f y| := by
    rw [ noiseOp_eq_kernel_sum ];
    exact le_trans ( Finset.abs_sum_le_sum_abs _ _ ) ( Finset.sum_le_sum fun y _ => by rw [ abs_mul, abs_of_nonneg ( noiseKernel_nonneg hρ0 hρ1 x y ) ] );
  have h_jensen : ConvexOn ℝ (Set.Ici 0) (fun x : ℝ => x ^ s) := by
    exact ( convexOn_rpow ( by linarith ) );
  refine' le_trans ( Real.rpow_le_rpow ( abs_nonneg _ ) h_triangle ( by positivity ) ) _;
  convert h_jensen.map_sum_le _ _ _ <;> norm_num;
  · exact fun y => noiseKernel_nonneg hρ0 hρ1 x y;
  · exact noiseKernel_sum_right hρ0 hρ1 x

/-
For any `s ≥ 1` and `0 ≤ ρ ≤ 1`, the noise operator is a contraction on Lˢ.
Uses Jensen's inequality on the noise kernel and the doubly stochastic property.
-/
/-- States the elementary `L^s` contraction estimate used in the duality argument.

**Source:** [OD14, Prop. 10.4 (proof)]. -/
lemma trivial_contractivity {n : ℕ} (s : ℝ) (hs : 1 ≤ s)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (f : BooleanFunc n) :
    (expect (fun x => |noiseOp ρ f x| ^ s)) ^ (1 / s) ≤
    (expect (fun x => |f x| ^ s)) ^ (1 / s) := by
  -- Using the inequality |T_ρ f(x)|^s ≤ ∑_y K(x,y) |f(y)|^s from `noiseOp_abs_rpow_le_kernel_avg`.
  have h_ineq : ∀ x : BoolCube n, |noiseOp ρ f x|^s ≤ ∑ y : BoolCube n, noiseKernel ρ x y * |f y|^s := by
    exact fun x => noiseOp_abs_rpow_le_kernel_avg hρ0 hρ1 s hs f x;
  refine' Real.rpow_le_rpow ( mul_nonneg ( by exact pow_nonneg ( by norm_num ) _ ) ( Finset.sum_nonneg fun _ _ => Real.rpow_nonneg ( abs_nonneg _ ) _ ) ) ( mul_le_mul_of_nonneg_left _ ( by exact pow_nonneg ( by norm_num ) _ ) ) ( by positivity );
  refine' le_trans ( Finset.sum_le_sum fun x _ => h_ineq x ) _;
  rw [ Finset.sum_comm ];
  simp +decide [← Finset.sum_mul, noiseKernel_sum_left hρ0 hρ1 ]

/-
Duality / Adjointness of operator norms
-/
/-- A cube noise-operator norm bound is equivalent to its Hölder-dual bound for finite
exponents `p,q > 1`. This is the finite cube specialization of the source's operator duality;
the conjugate endpoints `1` and `∞` are not represented here.

**Source:** [OD14, Prop. 10.4].

**Proof sketch.** Move noise between the two inner-product arguments by self-adjointness, then
apply Hölder and the assumed operator bound. Sharpness of Hölder recovers the noisy norm from
these pairing bounds. Repeat with conjugate exponents for the converse.
-/
lemma noise_op_norm_dual {n : ℕ} (p q : ℝ) (hp : 1 < p) (hq : 1 < q)
    (ρ : ℝ) (_hρ0 : 0 ≤ ρ) (_hρ1 : ρ ≤ 1) :
    (∀ f : BooleanFunc n,
      (expect (fun x => |noiseOp ρ f x| ^ q)) ^ (1 / q) ≤
      (expect (fun x => |f x| ^ p)) ^ (1 / p))
    ↔
    (∀ f : BooleanFunc n,
      (expect (fun x => |noiseOp ρ f x| ^ (p / (p - 1)))) ^ ((p - 1) / p) ≤
      (expect (fun x => |f x| ^ (q / (q - 1)))) ^ ((q - 1) / q)) := by
  constructor <;> intro h;
  · intro f
    have h_dual : ∀ g : BooleanFunc n, innerProduct g (noiseOp ρ f) ≤ (expect (fun x => |g x| ^ p)) ^ (1 / p) * (expect (fun x => |f x| ^ (q / (q - 1)))) ^ ((q - 1) / q) := by
      intro g
      have := h g
      have := h f
      simp_all;
      refine' le_trans _ ( mul_le_mul_of_nonneg_right ( h g ) _ );
      · convert holder_ineq_bool q hq ( noiseOp ρ g ) f using 1;
        · exact Eq.symm (noiseOp_self_adjoint ρ g f);
        · grind +splitImp;
      · exact Real.rpow_nonneg ( expect_rpow_abs_nonneg _ _ ) _;
    have := @holder_sharpness n ( p := p ) ( q := p / ( p - 1 ) ) ?_ ( noiseOp ρ f ) <;> norm_num at *;
    · obtain ⟨ g, hg₁, hg₂ ⟩ := this; exact hg₂.trans ( h_dual g |> le_trans <| mul_le_of_le_one_left ( by exact Real.rpow_nonneg ( by exact expect_rpow_abs_nonneg _ _ ) _ ) hg₁ ) ;
    · exact (Real.holderConjugate_iff_eq_conjExponent hp).mpr rfl;
  · intro f
    have h_dual : ∀ g : BooleanFunc n, innerProduct g (noiseOp ρ f) ≤ (expect (fun x => |g x| ^ (q / (q - 1)))) ^ ((q - 1) / q) * (expect (fun x => |f x| ^ p)) ^ (1 / p) := by
      -- Apply the hypothesis `h` to the function `g`.
      intros g
      have := h g;
      refine' le_trans _ ( mul_le_mul_of_nonneg_right this _ );
      · have := @holder_ineq_bool n ( p / ( p - 1 ) ) ?_ ( noiseOp ρ g ) f;
        · convert this using 1;
          · exact Eq.symm (noiseOp_self_adjoint ρ g f);
          · congr 1
            · congr 1
              have : p ≠ 0 := by linarith
              have : p - 1 ≠ 0 := by linarith
              field_simp;
            · congr 1
              · congr 1  -- <-- ADDED: Strips `expect`, leaving `(fun x => ...) = (fun x => ...)`
                ext x
                congr 1  -- Strips `|f x| ^`, leaving the exponent equality
                have : p ≠ 0 := by linarith
                have : p - 1 ≠ 0 := by linarith
                field_simp; ring
              · have : p ≠ 0 := by linarith
                have : p - 1 ≠ 0 := by linarith
                field_simp; ring
        · rw [ lt_div_iff₀ ] <;> linarith;
      · exact Real.rpow_nonneg ( expect_rpow_abs_nonneg _ _ ) _;
    have := @holder_sharpness n ( p := q / ( q - 1 ) ) ( q := q ) ?_ ( noiseOp ρ f ) <;> norm_num at *;
    · obtain ⟨ g, hg₁, hg₂ ⟩ := this; exact hg₂.trans ( h_dual g |> le_trans <| mul_le_of_le_one_left ( by exact Real.rpow_nonneg ( by exact expect_rpow_abs_nonneg _ _ ) _ ) hg₁ ) ;
    · constructor <;> norm_num [ hp, hq ];
      · rw [ inv_eq_one_div, ← add_div, div_eq_iff ] <;> linarith;
      · positivity;
      · positivity

/-- If `0 ≤ a ≤ b` and `b > 0`, then the square root of `a / b` is at most one. -/
lemma Interpolation.sqrt_div_le_one {a b : ℝ} (_ha : 0 ≤ a) (hb : 0 < b) (hab : a ≤ b) :
    Real.sqrt (a / b) ≤ 1 := by
  rw [Real.sqrt_le_one]
  exact div_le_one_iff.mpr (Or.inl ⟨hb, hab⟩)
private lemma noise_param_eq {p u : ℝ} (hu_pos : 0 < u - 1) :
    (u / (u - 1) - 1) * (p - 1) = (p - 1) / (u - 1) := by
  field_simp; ring
/--
**Bridging Case of One-Function Hypercontractivity.**
For `1 ≤ p ≤ 2 ≤ u` and `ρ = √((p-1)/(u-1))`:
  `(𝔼[|T_ρ f|^u])^{1/u} ≤ (𝔼[|f|^p])^{1/p}`
Derived by using `weak_two_function_hypercontractivity` with `p' = u/(u-1)` and `q' = p`
to get the two-function bound, then applying the backward direction of
`one_function_iff_two_function_hypercontractivity`.
**Source:** [OD14, Prop. 10.4].

**Proof sketch.** The conjugate exponent u/(u − 1) lies between one and two, so weak two-
function hypercontractivity applies to it and p. Its correlation simplifies to √((p − 1)/(u −
1)). Convert the pairing bound into the one-function bound.
-/
theorem bridging_hypercontractivity {n : ℕ}
    (p u : ℝ) (hp1 : 1 ≤ p) (hp2 : p ≤ 2) (hu : 2 ≤ u) (f : BooleanFunc n) :
    (expect (fun x => |noiseOp (Real.sqrt ((p - 1) / (u - 1))) f x| ^ u)) ^ (1 / u) ≤
    (expect (fun x => |f x| ^ p)) ^ (1 / p) := by
  set ρ := Real.sqrt ((p - 1) / (u - 1)) with hρ_def
  have hu_pos : 0 < u - 1 := by linarith
  have hp_sub : 0 ≤ p - 1 := by linarith
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρ1 : ρ ≤ 1 := Interpolation.sqrt_div_le_one hp_sub hu_pos (by linarith)
  have hu'1 : 1 ≤ u / (u - 1) := le_div_iff₀ hu_pos |>.mpr (by linarith)
  have hu'2 : u / (u - 1) ≤ 2 := div_le_iff₀ hu_pos |>.mpr (by linarith)
  have h_noise_eq : Real.sqrt ((u / (u - 1) - 1) * (p - 1)) = ρ := by
    congr 1; exact noise_param_eq hu_pos
  have h_two_func : ∀ (f g : BooleanFunc n),
      innerProduct f (noiseOp ρ g) ≤
      (expect (fun x => |f x| ^ (u / (u - 1)))) ^ ((u - 1) / u) *
      (expect (fun x => |g x| ^ p)) ^ (1 / p) := by
    intro f' g'
    have h := weak_two_function_hypercontractivity (u / (u - 1)) p hu'1 hu'2 hp1 hp2 f' g'
    rw [h_noise_eq] at h
    convert h using 2
    · congr 1; field_simp
  exact ((one_function_iff_two_function_hypercontractivity p u hp1 (le_trans hp2 hu) hu
    ρ hρ0 hρ1 (le_refl _)).mpr h_two_func) f

/--
Algebraic helper: all interpolation constraints for the low norms case.
Given `1 < p < u < 2` and `ρ² = (p-1)/(u-1)`, there exist `θ ∈ (0,1)` and `s > 0`
such that the interpolation equations hold.
Concretely, `θ = 2(u+p-2)/(pu)` and `s = 2-p`.
-/
private lemma low_norms_interpolation_params (p u ρ : ℝ) (hp : 1 < p) (hpu : p < u) (hu : u < 2)
    (hρ_sq : ρ ^ 2 = (p - 1) / (u - 1)) :
    ∃ θ s : ℝ, 0 < θ ∧ θ < 1 ∧ 0 < s ∧
    1 / p = θ / (1 + ρ ^ 2) + (1 - θ) / s ∧
    1 / u = θ / 2 + (1 - θ) / s := by
  refine' ⟨ 2 * ( u + p - 2 ) / ( p * u ), 2 - p, _, _, _, _, _ ⟩ <;> try nlinarith;
  · exact div_pos ( by linarith ) ( by nlinarith );
  · rw [ div_lt_iff₀ ] <;> nlinarith;
  · grind +splitIndPred;
  · grind

end BooleanAnalysis.Hypercontractivity
