/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import TCSlib.BooleanAnalysis.Hypercontractivity.Randomization.Basic
import TCSlib.BooleanAnalysis.Hypercontractivity.Products.Norms
import TCSlib.BooleanAnalysis.Hypercontractivity.Applications.LowDegree
import TCSlib.BooleanAnalysis.LMN.DecisionTreeFourier

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Supporting bounds for randomized low-degree projections

## Main definitions

No new definitions are introduced. This file uses finite-product norms,
orthogonal components, randomization, and cube low-degree projection.

## Main results

* `randomization_fourier_coefficient`: randomization's Walsh coefficients
  are the original product components.
* `RandomizationProjectionAux.cube_lowDegree_projection_noise_ge_two`:
  the cube projection-noise bound at every exponent at least two.
* `RandomizationProjectionAux.randomizationNorm_le_of_pointwise_cube_bound`:
  pointwise cube norm bounds lift to randomization norm bounds.
* `RandomizationProjectionAux.component_lowDegree`, `randomization_cube_noise`,
  `randomization_cube_lowDegree`, and `product_noise_lowDegree_commute`:
  spectral identities for the projections.
* `RandomizationProjectionAux.product_lowDegree_selfAdjoint` and
  `product_selfAdjoint_bound`: finite-product projection duality.
* `RandomizationProjectionAux.product_norm_const_mul`: norm homogeneity.

The supporting lemmas are collected in a dedicated auxiliary namespace.
The product low-degree projection theorem is in `Randomization.General`.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §8.3, Proposition 9.19, Theorem 9.21,
  Remark 10.33, Proposition 10.37, Lemma 10.38, and Theorem 10.39.
-/

open scoped BigOperators

namespace BooleanAnalysis.Hypercontractivity

open RandomizationAux

universe u

/-- At a fixed product input, each Walsh coefficient of the randomization is the
corresponding orthogonal component. [OD14, Rem. 10.33]

**Proof sketch.** Expand the finite Walsh sum and use orthogonality of the characters. -/
theorem randomization_fourier_coefficient {n : ℕ} (P : FiniteProduct.{u} n)
    (f : P.Point → ℝ) (x : P.Point) (S : Finset (Fin n)) :
    fourierCoeff (fun r => randomization P f r x) S = P.component S f x := by
  simpa only [randomization, mul_comm] using
    (DecisionTree.fourierCoeff_sum_chiS (fun T => P.component T f x) S)

namespace RandomizationProjectionAux

/-- Projection onto cube Fourier levels at most `k` has Fourier degree at most `k`.
[OD14, Prop. 10.37, proof]

**Proof sketch.** The projection's Fourier coefficients vanish on every set whose
cardinality exceeds the cutoff. -/
theorem cube_lowDegree_has_degree {n : ℕ} (f : BooleanFunc n) (k : ℕ) :
    has_degree_at_most (KKL.lowDegreePart f k) k := (by
  intro S hS
  by_contra hcard
  simp [KKL.fourierCoeff_lowDegreePart, hcard] at hS
)

/-- Projection onto cube Fourier levels at most `k` does not increase the second norm.
[OD14, Prop. 10.37, proof]

**Proof sketch.** Parseval expresses the squared second norm as a sum of squared Walsh
coefficients. Projection retains only terms below the cutoff, so discarding the other
nonnegative terms cannot increase the sum. Take square roots. -/
theorem cube_lowDegree_l2_le {n : ℕ} (f : BooleanFunc n) (k : ℕ) :
    l2Norm (KKL.lowDegreePart f k) ≤ l2Norm f := (by
  classical
  apply Real.sqrt_le_sqrt
  rw [parseval, parseval]
  apply Finset.sum_le_sum
  intro S _
  rw [KKL.fourierCoeff_lowDegreePart]
  split_ifs <;> simp [sq_nonneg]
)

/-- For every `q ≥ 2`, low-degree cube projection costs at most `(√(q-1)/ρ)^k`
relative to the `q`-norm of the noised function. [OD14, Lem. 10.38, proof;
Thm. 9.21] This extends the source's fourth-norm statement using general
low-degree hypercontractivity.

**Proof sketch.** Inverse noise recovers the projection from the projection of the
noised function. Bound its second norm using the degree cutoff, then apply
low-degree hypercontractivity, projection contractivity, and norm monotonicity. -/
theorem cube_lowDegree_projection_noise_ge_two {n : ℕ}
    (g : BooleanFunc n) (k : ℕ) (q : ℝ) (hq : 2 ≤ q)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    cubeLpNorm q (KKL.lowDegreePart g k) ≤
      (Real.sqrt (q - 1) / ρ) ^ k * cubeLpNorm q (noiseOp ρ g) := by
  classical
  let r : ℝ := 1 / ρ
  let f : BooleanFunc n := KKL.lowDegreePart (noiseOp ρ g) k
  have hr : 1 ≤ r := (le_div_iff₀ hρ).2 (by simpa using hρ1)
  have hcancel : noiseOp r f = KKL.lowDegreePart g k := by
    funext x
    change
      (∑ S : Finset (Fin n),
        r ^ S.card * fourierCoeff (KKL.lowDegreePart (noiseOp ρ g) k) S * chiS S x) =
      ∑ S : Finset (Fin n),
        if S.card ≤ k then fourierCoeff g S * chiS S x else 0
    apply Finset.sum_congr rfl
    intro S _
    rw [KKL.fourierCoeff_lowDegreePart, noiseOp_fourier]
    by_cases hS : S.card ≤ k
    · simp only [if_pos hS]
      rw [← mul_assoc, ← mul_pow, show r * ρ = 1 from one_div_mul_cancel hρ.ne']
      simp
    · simp [hS]
  calc
    cubeLpNorm q (KKL.lowDegreePart g k) ≤
        Real.sqrt (q - 1) ^ k * l2Norm (KKL.lowDegreePart g k) :=
      lowDegree_norm_ge_two _ (cube_lowDegree_has_degree g k) q hq
    _ = Real.sqrt (q - 1) ^ k * l2Norm (noiseOp r f) := by rw [hcancel]
    _ ≤ Real.sqrt (q - 1) ^ k * (r ^ k * l2Norm f) :=
      mul_le_mul_of_nonneg_left
        (l2Norm_noiseOp_le f (cube_lowDegree_has_degree (noiseOp ρ g) k) r hr)
        (by positivity)
    _ ≤ Real.sqrt (q - 1) ^ k * (r ^ k * cubeLpNorm q (noiseOp ρ g)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg (zero_le_one.trans hr) _)
      apply (cube_lowDegree_l2_le (noiseOp ρ g) k).trans
      rw [← cubeLpNorm_two]
      exact lp_norm_mono 2 q (by norm_num) hq (noiseOp ρ g)
    _ = (Real.sqrt (q - 1) / ρ) ^ k * cubeLpNorm q (noiseOp ρ g) := by
      rw [← mul_assoc, ← mul_pow]
      simp only [r, mul_one_div]

/-- Multiplying a function by a nonnegative constant scales its positive-exponent
product norm by that constant. [OD14, §8.1]

**Proof sketch.** Factor the constant's `q`th power out of the absolute moment, then
take the `1/q` power. -/
theorem product_norm_const_mul {n : ℕ} (P : FiniteProduct.{u} n)
    (q : ℝ) (hq : 0 < q) (a : ℝ) (ha : 0 ≤ a) (f : P.Point → ℝ) :
    P.norm q (fun x => a * f x) = a * P.norm q f := by
  have hmoment : 0 ≤ P.expect (fun x => |f x| ^ q) := by
    unfold FiniteProduct.expect
    apply Finset.sum_nonneg
    intro x _
    apply mul_nonneg _ (Real.rpow_nonneg (abs_nonneg _) _)
    unfold FiniteProduct.mass
    exact Finset.prod_nonneg fun i _ => (P.weight_pos i (x i)).le
  unfold FiniteProduct.norm
  simp_rw [abs_mul, abs_of_nonneg ha, Real.mul_rpow ha (abs_nonneg _)]
  rw [P.expect_const_mul, Real.mul_rpow (Real.rpow_nonneg ha q) hmoment]
  simp only [one_div, Real.rpow_rpow_inv ha hq.ne']

/-- A uniform bound on each input's cube randomization norm gives the same bound
after averaging over the product inputs. [OD14, Thm. 10.39, proof]

**Proof sketch.** Raise the pointwise inequalities to `q`, average their moment bounds,
and take the increasing `q`th root. -/
theorem randomizationNorm_le_of_pointwise_cube_bound {n : ℕ}
    (P : FiniteProduct.{u} n) (f g : P.Point → ℝ) (q A : ℝ)
    (hq : 0 < q) (hA : 0 ≤ A)
    (hbound : ∀ x, cubeLpNorm q (fun r => randomization P f r x) ≤
      A * cubeLpNorm q (fun r => randomization P g r x)) :
    randomizationNorm P q f ≤ A * randomizationNorm P q g := by
  classical
  have hmoment (h : P.Point → ℝ) :
      0 ≤ P.expect (fun x => expect (fun r => |randomization P h r x| ^ q)) :=
    Finset.sum_nonneg fun x _ =>
      mul_nonneg
        (Finset.prod_nonneg fun i _ => (P.weight_pos i (x i)).le)
        (expect_rpow_abs_nonneg q (fun r => randomization P h r x))
  unfold randomizationNorm
  calc
    (P.expect (fun x => expect (fun r => |randomization P f r x| ^ q))) ^ (1 / q) ≤
        (P.expect (fun x => A ^ q * expect (fun r => |randomization P g r x| ^ q))) ^
          (1 / q) := by
      apply Real.rpow_le_rpow (hmoment f) _ (one_div_nonneg.mpr hq.le)
      unfold FiniteProduct.expect
      apply Finset.sum_le_sum
      intro x _
      apply mul_le_mul_of_nonneg_left _
        (Finset.prod_nonneg fun i _ => (P.weight_pos i (x i)).le)
      have h := Real.rpow_le_rpow
        (Real.rpow_nonneg (expect_rpow_abs_nonneg q
          (fun r => randomization P f r x)) _) (hbound x) hq.le
      rw [cubeLpNorm_rpow _ q hq,
        Real.mul_rpow hA (Real.rpow_nonneg (expect_rpow_abs_nonneg q
          (fun r => randomization P g r x)) _),
        cubeLpNorm_rpow _ q hq] at h
      exact h
    _ = A * (P.expect (fun x => expect (fun r => |randomization P g r x| ^ q))) ^
        (1 / q) := by
      rw [P.expect_const_mul, Real.mul_rpow (Real.rpow_nonneg hA q) (hmoment g),
        ← Real.rpow_mul hA, mul_one_div_cancel hq.ne', Real.rpow_one]

/-- Projection onto degree at most `k` retains the component indexed by `S`
exactly when `S.card ≤ k`. [OD14, §8.3; §10.4]

**Proof sketch.** Express the degree cutoff as a finite linear combination with
indicator coefficients. Commute component projection through this combination and
use orthogonality of component projections; only the term indexed by `S` survives. -/
theorem component_lowDegree {n : ℕ} (P : FiniteProduct.{u} n)
    (S : Finset (Fin n)) (k : ℕ) (f : P.Point → ℝ) (x : P.Point) :
    P.component S (P.lowDegree k f) x =
      if S.card ≤ k then P.component S f x else 0 := by
  classical
  have hlow : P.lowDegree k f = fun y => ∑ T : Finset (Fin n),
      (if T.card ≤ k then (1 : ℝ) else 0) * P.component T f y := by
    funext y
    simp only [FiniteProduct.lowDegree, ite_mul, one_mul, zero_mul]
  rw [hlow]
  calc
    P.component S (fun y => ∑ T : Finset (Fin n),
        (if T.card ≤ k then (1 : ℝ) else 0) * P.component T f y) x =
        ∑ T : Finset (Fin n), (if T.card ≤ k then (1 : ℝ) else 0) *
          P.component S (P.component T f) x := by
      change (∑ U ∈ S.powerset, (-1 : ℝ) ^ (S.card - U.card) *
        P.expect (fun y => ∑ T : Finset (Fin n),
          (if T.card ≤ k then (1 : ℝ) else 0) * P.component T f
            (fun i => if i ∈ U then x i else y i))) = _
      simp_rw [P.expect_sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      change _ = ∑ T : Finset (Fin n), (if T.card ≤ k then (1 : ℝ) else 0) *
        ∑ U ∈ S.powerset,
          (-1 : ℝ) ^ (S.card - U.card) * P.condExp U (P.component T f) x
      simp only [FiniteProduct.condExp, Finset.mul_sum, mul_left_comm]
    _ = _ := by simp [component_component, mul_ite, ite_mul]

/-- At each product input, randomizing a noised function equals applying cube
noise to its sign variables. [OD14, Rem. 10.33; Def. 10.40]

**Proof sketch.** Both operations multiply the Walsh coefficient indexed by `S`
by `ρ ^ S.card`. Compare their finite spectral expansions term by term. -/
theorem randomization_cube_noise {n : ℕ} (P : FiniteProduct.{u} n)
    (ρ : ℝ) (f : P.Point → ℝ) (x : P.Point) :
    (fun r => randomization P (P.noise ρ f) r x) =
      noiseOp ρ (fun r => randomization P f r x) := by
  classical
  funext r
  simp only [noiseOp, randomization_fourier_coefficient]
  simp only [randomization, component_noise]
  apply Finset.sum_congr rfl
  intro S _
  ring

/-- At each product input, randomization commutes with projection onto degree
at most `k`. [OD14, Rem. 10.33; Prop. 10.37]

**Proof sketch.** The Walsh coefficients of randomization are the product
components. Both projections retain exactly the components whose index has
cardinality at most `k`. -/
theorem randomization_cube_lowDegree {n : ℕ} (P : FiniteProduct.{u} n)
    (k : ℕ) (f : P.Point → ℝ) (x : P.Point) :
    (fun r => randomization P (P.lowDegree k f) r x) =
      KKL.lowDegreePart (fun r => randomization P f r x) k := by
  classical
  funext r
  simp only [KKL.lowDegreePart, randomization_fourier_coefficient]
  simp only [randomization, component_lowDegree, mul_ite, mul_zero]
  apply Finset.sum_congr rfl
  intro S _
  split_ifs <;> ring

/-- Low-degree product projection is self-adjoint for the expectation pairing.
[OD14, §8.3; Thm. 10.39, proof]

**Proof sketch.** Expand the projection into its orthogonal components, then expand
each component as a finite linear combination of conditional expectations. Apply
the self-adjointness of conditional expectation term by term. -/
theorem product_lowDegree_selfAdjoint {n : ℕ} (P : FiniteProduct.{u} n)
    (k : ℕ) (f g : P.Point → ℝ) :
    P.expect (fun x => P.lowDegree k f x * g x) =
      P.expect (fun x => f x * P.lowDegree k g x) := by
  classical
  simp only [FiniteProduct.lowDegree, Finset.sum_mul, Finset.mul_sum, P.expect_sum]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hS : S.card ≤ k
  · simp only [if_pos hS]
    simp only [FiniteProduct.component, Finset.sum_mul, Finset.mul_sum, P.expect_sum]
    apply Finset.sum_congr rfl
    intro T _
    calc
      P.expect (fun x =>
          ((-1 : ℝ) ^ (S.card - T.card) * P.condExp T f x) * g x) =
          (-1 : ℝ) ^ (S.card - T.card) *
            P.expect (fun x => P.condExp T f x * g x) := by
        simpa only [mul_assoc] using
          P.expect_const_mul ((-1 : ℝ) ^ (S.card - T.card))
            (fun x => P.condExp T f x * g x)
      _ = (-1 : ℝ) ^ (S.card - T.card) *
            P.expect (fun x => f x * P.condExp T g x) := by
        rw [← P.condExp_selfAdjoint T f g]
      _ = P.expect (fun x =>
          f x * ((-1 : ℝ) ^ (S.card - T.card) * P.condExp T g x)) := by
        simpa only [mul_left_comm] using
          (P.expect_const_mul ((-1 : ℝ) ^ (S.card - T.card))
            (fun x => f x * P.condExp T g x)).symm
  · simp only [if_neg hS, zero_mul, mul_zero]

/-- Finite-product noise commutes with projection onto degree at most `k`, at
every real noise rate. [OD14, §8.3; Def. 10.40]

**Proof sketch.** Noise scales each component by its degree multiplier, while
projection retains components below the cutoff. These componentwise operations commute. -/
theorem product_noise_lowDegree_commute {n : ℕ} (P : FiniteProduct.{u} n)
    (ρ : ℝ) (k : ℕ) (f : P.Point → ℝ) :
    P.noise ρ (P.lowDegree k f) = P.lowDegree k (P.noise ρ f) := by
  classical
  funext x
  change (∑ S : Finset (Fin n),
      ρ ^ S.card * P.component S (P.lowDegree k f) x) =
    ∑ S : Finset (Fin n),
      if S.card ≤ k then P.component S (P.noise ρ f) x else 0
  simp only [component_lowDegree, component_noise, mul_ite, mul_zero]

/-- A bound for a self-adjoint operator in the conjugate product norm gives the
same bound in the original norm. [OD14, Prop. 9.19, proof]
This isolates the scaled operator duality argument.

**Proof sketch.** Divide the operator by the positive bound, apply self-adjoint
contraction duality, and multiply the resulting inequality by the bound. -/
theorem product_selfAdjoint_bound {n : ℕ} (P : FiniteProduct.{u} n)
    (T : (P.Point → ℝ) → P.Point → ℝ)
    (hself : ∀ f g : P.Point → ℝ,
      P.expect (fun x => T f x * g x) = P.expect (fun x => f x * T g x))
    (q : ℝ) (hq : 1 < q) (A : ℝ) (hA : 0 < A)
    (hbound : ∀ g : P.Point → ℝ, P.norm (q / (q - 1)) (T g) ≤
      A * P.norm (q / (q - 1)) g) :
    ∀ f : P.Point → ℝ, P.norm q (T f) ≤ A * P.norm q f := (by
  classical
  intro f
  let U : (P.Point → ℝ) → P.Point → ℝ := fun g x => A⁻¹ * T g x
  have hsmall : P.norm q (U f) ≤ P.norm q f := by
    unfold FiniteProduct.norm FiniteProduct.expect
    refine FiniteNorms.selfAdjoint_contraction P.mass
      (fun x => Finset.prod_nonneg fun i _ => (P.weight_pos i (x i)).le)
      U ?_ q hq ?_ f
    · intro g h
      simpa only [FiniteProduct.expect, U, Finset.mul_sum, mul_assoc, mul_left_comm] using
        congrArg (fun z : ℝ => A⁻¹ * z) (hself g h)
    · intro g
      change P.norm (q / (q - 1)) (fun x => A⁻¹ * T g x) ≤
        P.norm (q / (q - 1)) g
      rw [product_norm_const_mul P (q / (q - 1))
        (div_pos (lt_trans zero_lt_one hq) (sub_pos.mpr hq))
        A⁻¹ (inv_nonneg.mpr hA.le) (T g)]
      calc
        A⁻¹ * P.norm (q / (q - 1)) (T g) ≤
            A⁻¹ * (A * P.norm (q / (q - 1)) g) :=
          mul_le_mul_of_nonneg_left (hbound g) (inv_nonneg.mpr hA.le)
        _ = P.norm (q / (q - 1)) g := by
          rw [← mul_assoc, inv_mul_cancel₀ hA.ne', one_mul]
  change P.norm q (fun x => A⁻¹ * T f x) ≤ P.norm q f at hsmall
  rw [product_norm_const_mul P q (lt_trans zero_lt_one hq)
    A⁻¹ (inv_nonneg.mpr hA.le) (T f)] at hsmall
  simpa only [← mul_assoc, mul_inv_cancel₀ hA.ne', one_mul] using
    mul_le_mul_of_nonneg_left hsmall hA.le
)

end RandomizationProjectionAux

end BooleanAnalysis.Hypercontractivity
