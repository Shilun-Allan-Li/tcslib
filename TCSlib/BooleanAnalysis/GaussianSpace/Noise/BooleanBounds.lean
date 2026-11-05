/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.Hypercontractivity.Cube.General.Bounds

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Boolean pairing estimates for Gaussian approximation

## Main definitions

The existing Boolean cube expectation, noise operator and inner product are reused.

## Main results

* `boolean_two_function_smallOffset`: the two-function estimate with positive
  exponent offsets, when the first offset is at most one.
* `boolean_two_function_positiveOffsets`: the symmetric positive-offset estimate.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §10.1, Proposition 10.4, and §11.1,
  Gaussian Hypercontractivity.
-/

namespace BooleanAnalysis.GaussianSpace

open Hypercontractivity

/-- Positive exponent offsets with product at most one give the Boolean
two-function estimate whenever the first offset is at most one and the squared
correlation is bounded by their product.
[OD14, §10.1, Prop. 10.4; §11.1, Gaussian Hypercontractivity]

**Proof sketch.** Apply the existing two-function theorem with input exponent
`1+s` and output exponent `(1+r)/r`. Its dual exponent is `1+r`, and its
correlation threshold is the square root of `r*s`. -/
lemma boolean_two_function_smallOffset {n : ℕ} (r s ρ : ℝ)
    (hr : 0 < r) (hs : 0 < s) (hr1 : r ≤ 1) (hrs : r * s ≤ 1)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hρsq : ρ ^ 2 ≤ r * s)
    (f g : BooleanFunc n) :
    innerProduct f (noiseOp ρ g) ≤
      (expect (fun x => |f x| ^ (1 + r))) ^ (1 / (1 + r)) *
        (expect (fun x => |g x| ^ (1 + s))) ^ (1 / (1 + s)) := by
  let u : ℝ := (1 + r) / r
  have hu : 2 ≤ u := by
    dsimp [u]
    apply (le_div_iff₀ hr).2
    linarith
  have hpu : 1 + s ≤ u := by
    dsimp [u]
    apply (le_div_iff₀ hr).2
    nlinarith [hrs]
  have hsub : u - 1 = 1 / r := by
    dsimp [u]
    field_simp [hr.ne']
    ring
  have hratio : ((1 + s) - 1) / (u - 1) = r * s := by
    rw [hsub]
    field_simp [hr.ne']
    ring
  have hdual : u / (u - 1) = 1 + r := by
    rw [hsub]
    dsimp [u]
    field_simp [hr.ne']
  have hpower : (u - 1) / u = 1 / (1 + r) := by
    rw [hsub]
    dsimp [u]
    field_simp [hr.ne', show 1 + r ≠ 0 by linarith]
  have h := general_two_function_hypercontractivity
    (1 + s) u (by linarith) hpu hu ρ hρ0 hρ1
    (by rw [hratio]; exact Real.le_sqrt_of_sq_le hρsq) f g
  simpa only [hdual, hpower] using h

/-- Positive exponent offsets with product at most one give the Boolean
two-function estimate when the squared correlation is bounded by their product.
[OD14, §10.1, Prop. 10.4; §11.1, Gaussian Hypercontractivity]

**Proof sketch.** At least one offset is at most one. Apply the preceding
estimate directly when the first is small; otherwise interchange the functions
and offsets, using symmetry and self-adjointness of Boolean noise. -/
lemma boolean_two_function_positiveOffsets {n : ℕ} (r s ρ : ℝ)
    (hr : 0 < r) (hs : 0 < s) (hrs : r * s ≤ 1)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hρsq : ρ ^ 2 ≤ r * s)
    (f g : BooleanFunc n) :
    innerProduct f (noiseOp ρ g) ≤
      (expect (fun x => |f x| ^ (1 + r))) ^ (1 / (1 + r)) *
        (expect (fun x => |g x| ^ (1 + s))) ^ (1 / (1 + s)) := by
  by_cases hr1 : r ≤ 1
  · exact boolean_two_function_smallOffset r s ρ hr hs hr1 hrs hρ0 hρ1 hρsq f g
  · have hs1 : s ≤ 1 := by nlinarith
    calc
      innerProduct f (noiseOp ρ g) = innerProduct g (noiseOp ρ f) := by
        rw [innerProduct_comm, noiseOp_self_adjoint]
      _ ≤ (expect (fun x => |g x| ^ (1 + s))) ^ (1 / (1 + s)) *
          (expect (fun x => |f x| ^ (1 + r))) ^ (1 / (1 + r)) :=
        boolean_two_function_smallOffset s r ρ hs hr hs1
          (by simpa only [mul_comm] using hrs) hρ0 hρ1
          (by simpa only [mul_comm] using hρsq) g f
      _ = _ := mul_comm _ _

end BooleanAnalysis.GaussianSpace
