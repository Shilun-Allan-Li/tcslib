/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Finite-space noise duality

This module proves self-adjoint duality for finite weighted noise operators using
a scalar signed-power witness. The argument in Proposition 9.19
is used by Exercise 10.20 to obtain the `(2, q)` bound in Theorem 10.18; Exercise 10.19
supplies the surrounding finite-space reduction.

## Main definitions

No new definitions are introduced. The signed witness is a local expression in
`signed_power_dual`.

## Main results

* `signed_power_dual`: the pairing and conjugate-power identities for the signed witness
  `z * |z| ^ (q - 2)`, for every real `q > 2` and real `z`.
* `finite_noise_identities`: the second-moment and self-adjoint pairing identities for
  finite weighted noise.
* `finite_noise_duality`: conjugate-to-two contraction implies two-to-`q` contraction
  on the entire finite weighted function space.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014;
  May 2021 arXiv edition, Proposition 9.19 (proof), Theorem 10.18, and Exercises 10.19–10.20.
-/

open scoped BigOperators

namespace BooleanAnalysis.Hypercontractivity.SharpDiscrete

/-- For every real exponent `q > 2` and real number `z`, the signed witness
`g = z * |z| ^ (q - 2)` satisfies `z * g = |z| ^ q` and
`|g| ^ (q / (q - 1)) = |z| ^ q`, including when `z` is zero or negative.
This technical scalar identity isolates the Hölder equality calculation in
[OD14, Prop. 9.19 (proof)], used in [OD14, Ex. 10.20] toward [OD14, Thm. 10.18].

**Proof sketch.** Treat `z = 0` first; all relevant exponents are positive because
`q > 2`. Otherwise `|z| > 0`. Rewrite `z * z` as `|z|²` and add real exponents
to obtain the first identity. The real power of `|z|` is nonnegative, so taking the
absolute value of the witness gives `|g| = |z|^(q - 1)`. Multiply exponents and use
`(q - 1) * (q / (q - 1)) = q` to obtain the second identity. -/
theorem signed_power_dual (q : ℝ) (hq : 2 < q) (z : ℝ) :
    let g : ℝ := z * |z| ^ (q - 2)
    z * g = |z| ^ q ∧ |g| ^ (q / (q - 1)) = |z| ^ q := by
  have hq0 : q ≠ 0 := by linarith
  have hq1 : q - 1 ≠ 0 := by linarith
  dsimp only
  by_cases hz : z = 0
  · subst z
    simp [Real.zero_rpow hq0, Real.zero_rpow (div_ne_zero hq0 hq1)]
  · have hzpos : 0 < |z| := abs_pos.mpr hz
    constructor
    · calc
        z * (z * |z| ^ (q - 2)) = |z| ^ (2 : ℝ) * |z| ^ (q - 2) := by
          rw [Real.rpow_two, sq_abs, pow_two]
          ring
        _ = |z| ^ (2 + (q - 2)) := (Real.rpow_add hzpos 2 (q - 2)).symm
        _ = |z| ^ q := by congr 1; ring
    · have habs : |z * |z| ^ (q - 2)| = |z| ^ (q - 1) := by
        calc
          |z * |z| ^ (q - 2)| = |z| ^ (1 : ℝ) * |z| ^ (q - 2) := by
            rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg z) _),
              Real.rpow_one]
          _ = |z| ^ (1 + (q - 2)) := (Real.rpow_add hzpos 1 (q - 2)).symm
          _ = |z| ^ (q - 1) := by congr 1; ring
      rw [habs, ← Real.rpow_mul (abs_nonneg z)]
      congr 1
      rw [← mul_div_assoc, mul_div_cancel_left₀ q hq1]
/-- For any finite family of real weights summing to one, the affine noise transform
`g i ↦ ρ * g i + (1 - ρ) * mg` has weighted second moment
`ρ² ∑ i, w i * (g i)² + (1 - ρ²) * mg²`, and moving this transform between
the two factors preserves their weighted pairing. Here `mf` and `mg` are
the weighted means of `f` and `g`.

These technical algebraic identities support the self-adjoint duality calculation in
[OD14, Prop. 9.19 (proof)] and [OD14, Ex. 10.20], in the finite-space setting of
[OD14, Ex. 10.19] and [OD14, Thm. 10.18]. The formulation allows signed weights
and arbitrary real noise parameters because positivity is unnecessary for these identities.

**Proof sketch.** Expand the square and distribute the finite sum. Factor out
the constant coefficients, replace the weighted sum of `g` by its mean, and
use total weight one to simplify the constant term. For the pairing identity,
expand both transforms and factor the resulting sums; both sides have the
same mixed moment and the same product of weighted means. -/
theorem finite_noise_identities {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw : ∑ i, w i = 1) (ρ : ℝ) (f g : ι → ℝ) :
    let mf : ℝ := ∑ i, w i * f i
    let mg : ℝ := ∑ i, w i * g i
    (∑ i, w i * (ρ * g i + (1 - ρ) * mg) ^ 2) =
      ρ ^ 2 * (∑ i, w i * (g i) ^ 2) + (1 - ρ ^ 2) * mg ^ 2 ∧
    (∑ i, w i * (ρ * f i + (1 - ρ) * mf) * g i) =
      ∑ i, w i * f i * (ρ * g i + (1 - ρ) * mg) := by
  intro mf mg
  constructor
  · calc
      (∑ i, w i * (ρ * g i + (1 - ρ) * mg) ^ 2) =
          ∑ i, (ρ ^ 2 * (w i * (g i) ^ 2) +
            (2 * ρ * (1 - ρ) * mg) * (w i * g i) +
            ((1 - ρ) ^ 2 * mg ^ 2) * w i) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = ρ ^ 2 * (∑ i, w i * (g i) ^ 2) +
          (2 * ρ * (1 - ρ) * mg) * mg + (1 - ρ) ^ 2 * mg ^ 2 := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hw, mul_one]
        rfl
      _ = ρ ^ 2 * (∑ i, w i * (g i) ^ 2) +
          (1 - ρ ^ 2) * mg ^ 2 := by
        ring
  · calc
      (∑ i, w i * (ρ * f i + (1 - ρ) * mf) * g i) =
          ∑ i, (ρ * (w i * f i * g i) +
            ((1 - ρ) * mf) * (w i * g i)) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = ρ * (∑ i, w i * f i * g i) + (1 - ρ) * mf * mg := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
        rfl
      _ = ρ * (∑ i, w i * f i * g i) + ((1 - ρ) * mg) * mf := by
        ring
      _ = ∑ i, (ρ * (w i * f i * g i) +
          ((1 - ρ) * mg) * (w i * f i)) := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
        rfl
      _ = ∑ i, w i * f i * (ρ * g i + (1 - ρ) * mg) := by
        apply Finset.sum_congr rfl
        intro i _
        ring

/-- On a finite probability space with nonnegative weights summing to one, let
`p = q / (q - 1)` for a real exponent `q > 2`. If the affine noise transform
`Tρ g i = ρ * g i + (1 - ρ) * ∑ j, w j * g j` has squared weighted `L²` norm
at most the squared weighted `Lᵖ` norm of every real function `g`, then the
squared weighted `Lᑫ` norm of `Tρ f` is at most the squared weighted `L²` norm
of every real function `f`.

This is the finite weighted form of the self-adjoint operator duality argument
in [OD14, Prop. 9.19 (proof)], used by [OD14, Ex. 10.20] toward
[OD14, Thm. 10.18], with the finite-space setting supplied by [OD14, Ex. 10.19].
The norms and noise transform are expanded into finite sums. The restriction to
finite real `q > 2` is retained from the intended application. Zero weights are
permitted, and the parameter `ρ` may be any real number because the implication
uses self-adjointness, which holds for every real `ρ`.

**Proof sketch.** For a given `f`, write `z = Tρ f` and take the signed dual
witness `g i = z i * |z i| ^ (q - 2)`. The scalar signed-power identities show
that both the weighted pairing of `z` with `g` and the weighted `p`-moment of
`g` equal `M = ∑ i, w i * |z i| ^ q`. Move the noise transform across the
pairing using the finite-noise self-adjoint identity. Weighted Cauchy–Schwarz
then bounds `M²` by the second moment `A` of `f` times the second moment of
`Tρ g`. The finite-noise quadratic identity and the assumed contraction bound
give `M² ≤ A * M^(2/p)`. If `M > 0`, use `2/q + 2/p = 2` to cancel the positive
factor `M^(2/p)` and obtain `M^(2/q) ≤ A`. If `M = 0`, positivity of `q` and
nonnegativity of `A` give the conclusion directly. -/
theorem finite_noise_duality {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw_nonneg : ∀ i, 0 ≤ w i) (hw : ∑ i, w i = 1)
    (q : ℝ) (hq : 2 < q) (ρ : ℝ)
    (hcontract : ∀ g : ι → ℝ,
      ρ ^ 2 * (∑ i, w i * (g i) ^ 2) +
          (1 - ρ ^ 2) * (∑ i, w i * g i) ^ 2 ≤
        (∑ i, w i * |g i| ^ (q / (q - 1))) ^ (2 / (q / (q - 1)))) :
    ∀ f : ι → ℝ,
      (∑ i, w i *
        |ρ * f i + (1 - ρ) * (∑ j, w j * f j)| ^ q) ^ (2 / q) ≤
        ∑ i, w i * (f i) ^ 2 := by
  intro f
  let p : ℝ := q / (q - 1)
  let z : ι → ℝ := fun i => ρ * f i + (1 - ρ) * (∑ j, w j * f j)
  let g : ι → ℝ := fun i => z i * |z i| ^ (q - 2)
  let H : ι → ℝ := fun i => ρ * g i + (1 - ρ) * (∑ j, w j * g j)
  let M : ℝ := ∑ i, w i * |z i| ^ q
  let A : ℝ := ∑ i, w i * (f i) ^ 2
  change M ^ (2 / q) ≤ A
  have hqpos : 0 < q := by linarith
  have hMnonneg : 0 ≤ M :=
    Finset.sum_nonneg fun i _ =>
      mul_nonneg (hw_nonneg i) (Real.rpow_nonneg (abs_nonneg (z i)) q)
  have hAnonneg : 0 ≤ A :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hw_nonneg i) (sq_nonneg (f i))
  -- The signed witness realizes both the pairing and the conjugate moment.
  have hpair : (∑ i, w i * f i * H i) = M := by
    calc
      (∑ i, w i * f i * H i) = ∑ i, w i * z i * g i :=
        (finite_noise_identities w hw ρ f g).2.symm
      _ = M := by
        apply Finset.sum_congr rfl
        intro i _
        rw [mul_assoc]
        congr 1
        exact (signed_power_dual q hq (z i)).1
  have hmoment : (∑ i, w i * |g i| ^ p) = M := by
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    exact (signed_power_dual q hq (z i)).2
  have hHbound : (∑ i, w i * (H i) ^ 2) ≤ M ^ (2 / p) := by
    calc
      (∑ i, w i * (H i) ^ 2) =
          ρ ^ 2 * (∑ i, w i * (g i) ^ 2) +
            (1 - ρ ^ 2) * (∑ i, w i * g i) ^ 2 :=
        (finite_noise_identities w hw ρ f g).1
      _ ≤ M ^ (2 / p) := by
        rw [← hmoment]
        exact hcontract g
  -- Weighted Cauchy–Schwarz converts the pairing into a moment bound.
  have hCS : M ^ 2 ≤ A * (∑ i, w i * (H i) ^ 2) := by
    rw [← hpair]
    simpa only [A] using
      Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul (Finset.univ : Finset ι)
        (r := fun i => w i * f i * H i)
        (f := fun i => w i * (f i) ^ 2)
        (g := fun i => w i * (H i) ^ 2)
        (fun i _ => mul_nonneg (hw_nonneg i) (sq_nonneg (f i)))
        (fun i _ => mul_nonneg (hw_nonneg i) (sq_nonneg (H i)))
        (fun i _ => by ring)
  have hbound : M ^ 2 ≤ A * M ^ (2 / p) :=
    hCS.trans (mul_le_mul_of_nonneg_left hHbound hAnonneg)
  by_cases hMzero : M = 0
  · rw [hMzero, Real.zero_rpow (div_ne_zero (by norm_num) hqpos.ne')]
    exact hAnonneg
  · have hMpos : 0 < M := lt_of_le_of_ne hMnonneg (Ne.symm hMzero)
    have hexponents : 2 / q + 2 / p = 2 := by
      have hqone : q - 1 ≠ 0 := by linarith
      dsimp only [p]
      field_simp [hqpos.ne', hqone]
      <;> ring
    apply le_of_mul_le_mul_right
      (a := M ^ (2 / p)) ?_ (Real.rpow_pos_of_pos hMpos (2 / p))
    calc
      M ^ (2 / q) * M ^ (2 / p) = M ^ 2 := by
        rw [← Real.rpow_add hMpos, hexponents, Real.rpow_two]
      _ ≤ A * M ^ (2 / p) := hbound


end BooleanAnalysis.Hypercontractivity.SharpDiscrete
