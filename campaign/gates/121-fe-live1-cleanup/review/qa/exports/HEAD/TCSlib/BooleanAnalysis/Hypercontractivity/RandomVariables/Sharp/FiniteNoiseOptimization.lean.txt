/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.Compact
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Convex.Function
import Mathlib.Data.Finset.Max
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Finite-space noise optimization

This module provides compactness ingredients for finite-space optimizer and
variational reductions in sharp discrete hypercontractivity.

## Main definitions

No new definitions are introduced.

## Main results

* `finite_moment_sphere_compact`: the unit weighted real-moment level set is
  compact for a finite index type, strictly positive weights, and a positive exponent.
* `exists_nonnegative_noise_maximizer`: a nonnegative unit-moment function maximizes
  the quadratic noise objective on a finite weighted probability space.
* `finite_concave_level_two_values`: finite nonnegative values in a common strictly
  concave level set are supported on at most two points.
* `finite_noise_homogeneity`: scaling identities for the weighted moment and
  quadratic noise objective.
* `derivative_eq_mul_of_isLocalMax_quotient`: the derivative equation for a
  normalized quotient at a local maximum.
* `finite_noise_normalization`: normalization to unit weighted moment and the
  resulting quotient formula for the noise objective.
* `finite_noise_directional_derivatives`: derivatives of the moment and
  quadratic noise objective along affine finite-space paths.
* `finite_noise_maximizer_stationarity`: the stationary equation for a
  nonnegative unit-moment maximizer, with objective value at least one.
* `finite_noise_maximizer_two_values`: every such nonnegative maximizer is
  supported on at most two values.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014, Exercise 10.19(a)–(g), supporting the finite-space reduction for Theorem 10.18.
-/

open scoped BigOperators Topology

namespace BooleanAnalysis.Hypercontractivity.SharpDiscrete

/-- For a finite index type, strictly positive real weights, and a real exponent
`p > 0`, the set of real functions whose weighted absolute `p` moment equals one
is compact in the product topology.

This is the compactness ingredient in [OD14, Exercise 10.19(b)], supporting
[OD14, Theorem 10.18]. For this technical ingredient, the source range `1 < p < 2`
is extended to `p > 0`: continuity and coordinate bounds require only positivity
of the exponent. Neither normalized weights nor a nonempty index type are assumed;
the level set is allowed to be empty.

**Proof sketch.** The weighted moment map is continuous because coordinate
evaluation, absolute value, positive real powers, and finite sums are continuous.
Its level set at one is therefore closed. Each weighted summand is nonnegative,
so a function in the level set satisfies `w i * |f i| ^ p ≤ 1` at every coordinate.
Divide by the positive weight and take the positive inverse power to obtain
`|f i| ≤ (1 / w i) ^ (1 / p)`. Thus the level set lies in the product of the
corresponding symmetric closed intervals. This product is compact, so its closed
subset given by the unit-moment level set is compact. -/
theorem finite_moment_sphere_compact {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (p : ℝ) (hp : 0 < p) :
    IsCompact {f : ι → ℝ | (∑ i, w i * |f i| ^ p) = 1} := by
  classical
  let B : ι → ℝ := fun i => (1 / w i) ^ p⁻¹
  have hcontinuous : Continuous (fun f : ι → ℝ => ∑ i, w i * |f i| ^ p) := by
    refine continuous_finset_sum _ fun i _ => ?_
    exact continuous_const.mul
      ((Real.continuous_rpow_const hp.le).comp (continuous_apply i).abs)
  refine (isCompact_Icc (a := fun i => -B i) (b := B)).of_isClosed_subset
    (isClosed_eq hcontinuous continuous_const) ?_
  intro f hf
  have hbound : ∀ i, |f i| ≤ B i := by
    intro i
    apply (Real.le_rpow_inv_iff_of_pos (abs_nonneg _)
      (div_nonneg zero_le_one (hw i).le) hp).2
    apply (le_div_iff₀ (hw i)).2
    rw [mul_comm]
    calc
      w i * |f i| ^ p ≤ ∑ j, w j * |f j| ^ p :=
        Finset.single_le_sum
          (fun j _ => mul_nonneg (hw j).le (Real.rpow_nonneg (abs_nonneg _) _))
          (Finset.mem_univ i)
      _ = 1 := hf
  exact ⟨fun i => (abs_le.mp (hbound i)).1, fun i => (abs_le.mp (hbound i)).2⟩


/-- For a finite index type with strictly positive real weights summing to one,
`1 < p < 2`, and `0 ≤ ρ ≤ 1`, there exists a nonnegative function of unit weighted
absolute `p` moment maximizing the squared output `2` norm of the noise operator
among all real functions with that same normalization.

This is the optimizer reduction in [OD14, Exercise 10.19(b)–(c)], supporting
[OD14, Theorem 10.18]. The ingested source's inconsistent minimization/maximization
wording is corrected here by maximizing the squared output norm subject to unit
input `p` moment. No separate nonemptiness hypothesis on the index type is needed:
the normalized weights make the constant-one function admissible.
The source's radius range is extended to include `ρ = 0`, where the same
compactness and absolute-value comparison apply.

**Proof sketch.** The unit weighted moment level set is compact by
`finite_moment_sphere_compact` and contains the constant-one function. The noise
objective is continuous, so it attains a maximum on this set. Taking coordinatewise
absolute values preserves the weighted absolute `p` moment and the weighted second
moment. The triangle inequality for the weighted sum shows that the squared mean
cannot decrease, and its coefficient `1 - ρ²` is nonnegative. Hence taking absolute
values of a maximizer produces a nonnegative maximizer with the same normalization. -/
theorem exists_nonnegative_noise_maximizer {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (hw_sum : ∑ i, w i = 1)
    (p ρ : ℝ) (hp_one : 1 < p) (hp_two : p < 2)
    (hρ_nonneg : 0 ≤ ρ) (hρ_le_one : ρ ≤ 1) :
    let G : (ι → ℝ) → ℝ := fun f => ∑ i, w i * |f i| ^ p
    let F : (ι → ℝ) → ℝ := fun f =>
      ρ ^ (2 : ℕ) * (∑ i, w i * f i ^ (2 : ℕ)) +
        (1 - ρ ^ (2 : ℕ)) * (∑ i, w i * f i) ^ (2 : ℕ)
    ∃ g : ι → ℝ, (∀ i, 0 ≤ g i) ∧ G g = 1 ∧
      ∀ f : ι → ℝ, G f = 1 → F f ≤ F g := by
  classical
  intro G F
  have hcontinuous : Continuous F := by
    dsimp only [F]
    exact (continuous_const.mul
      (continuous_finset_sum _ fun i _ =>
        continuous_const.mul ((continuous_apply i).pow 2))).add
      (continuous_const.mul
        ((continuous_finset_sum _ fun i _ =>
          continuous_const.mul (continuous_apply i)).pow 2))
  obtain ⟨f, hf, hmax⟩ :=
    (finite_moment_sphere_compact w hw p (lt_trans zero_lt_one hp_one)).exists_isMaxOn
      ⟨fun _ => 1, by simpa using hw_sum⟩ hcontinuous.continuousOn
  have hcoeff : 0 ≤ 1 - ρ ^ (2 : ℕ) := by
    nlinarith [mul_nonneg hρ_nonneg (sub_nonneg.mpr hρ_le_one)]
  refine ⟨fun i => |f i|, fun i => abs_nonneg _, ?_, ?_⟩
  · simpa only [G, abs_abs] using hf
  · intro k hk
    calc
      F k ≤ F f := hmax hk
      _ ≤ F (fun i => |f i|) := by
        have hmean : |∑ i, w i * f i| ≤ ∑ i, w i * |f i| := by
          calc
            |∑ i, w i * f i| ≤ ∑ i, |w i * f i| :=
              Finset.abs_sum_le_sum_abs _ _
            _ = ∑ i, w i * |f i| := by
              apply Finset.sum_congr rfl
              intro i _
              rw [abs_mul, abs_of_pos (hw i)]
        have hmean_sq :
            (∑ i, w i * f i) ^ (2 : ℕ) ≤
              (∑ i, w i * |f i|) ^ (2 : ℕ) := by
          simpa only [sq_abs] using
            (sq_le_sq₀ (abs_nonneg _)
              (Finset.sum_nonneg fun i _ =>
                mul_nonneg (hw i).le (abs_nonneg _))).2 hmean
        dsimp only [F]
        simp only [sq_abs]
        exact add_le_add_left (mul_le_mul_of_nonneg_left hmean_sq hcoeff) _



/-- A nonnegative real-valued function on a finite type whose values lie in one
level set of a strictly concave function on `[0, ∞)` takes at most two values,
both nonnegative.

This is a technical root-counting reformulation of [OD14, Exercise 10.19(g)],
supporting [OD14, Theorem 10.18]. Strict concavity is assumed directly, so no
weights or moment normalization are needed. Zero inputs are included because
strict concavity is available on the whole nonnegative half-line. The index
type may be empty.

**Proof sketch.** For an empty index type, choose both values to be zero.
Otherwise, choose the minimum and maximum values of the finite function.
Every value lies between these endpoints. A value different from both
endpoints lies in their open segment, where strict concavity makes its image
strictly larger than the common image of the endpoints. This contradicts the
level-set hypothesis, so every value equals one of the endpoints. -/
theorem finite_concave_level_two_values {ι : Type*} [Fintype ι]
    (φ : ℝ → ℝ) (hφ : StrictConcaveOn ℝ (Set.Ici 0) φ)
    (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i)
    (c : ℝ) (hlevel : ∀ i, φ (f i) = c) :
    ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ ∀ i, f i = a ∨ f i = b := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · letI := hι
    exact ⟨0, 0, le_rfl, le_rfl, fun i => isEmptyElim i⟩
  · letI := hι
    obtain ⟨x, _, hx⟩ :=
      Finset.exists_min_image (Finset.univ : Finset ι) f Finset.univ_nonempty
    obtain ⟨y, _, hy⟩ :=
      Finset.exists_max_image (Finset.univ : Finset ι) f Finset.univ_nonempty
    refine ⟨f x, f y, hf x, hf y, ?_⟩
    intro i
    by_cases hix : f i = f x
    · exact Or.inl hix
    by_cases hiy : f i = f y
    · exact Or.inr hiy
    have hxi : f x < f i :=
      lt_of_le_of_ne (hx i (Finset.mem_univ i)) (Ne.symm hix)
    have hiy' : f i < f y :=
      lt_of_le_of_ne (hy i (Finset.mem_univ i)) hiy
    have hcontra := hφ.lt_on_openSegment (hf x) (hf y)
      (ne_of_lt (lt_trans hxi hiy')) (Ioo_subset_openSegment ⟨hxi, hiy'⟩)
    rw [hlevel x, hlevel y, hlevel i, min_self] at hcontra
    exact (lt_irrefl c hcontra).elim



/-- Scaling a real-valued function on a finite type by any real scalar `t`
multiplies its weighted absolute `p` moment by `|t| ^ p` and its quadratic noise
objective `ρ² ∑ i, w i * f i² + (1 - ρ²) (∑ i, w i * f i)²` by `t²`.

These are technical homogeneity identities used in [OD14, Exercise 10.19(a),
(c)–(e)], supporting [OD14, Theorem 10.18]. For this finite-sum helper, the
source's positive normalized weights, exponent range, and noise-radius range
are extended to arbitrary real weights and parameters because both identities
are algebraic. Signed function values, a zero scalar, and an empty index type
are included.

**Proof sketch.** Rewrite the absolute value of each scalar product as the
product of absolute values. Multiplicativity of real powers on nonnegative
bases extracts the common factor `|t| ^ p` from the weighted moment sum.
For the quadratic objective, extract `t²` from the weighted second moment
and `t` from the weighted mean; squaring the latter and factoring gives
the common factor `t²`. -/
theorem finite_noise_homogeneity {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (p ρ t : ℝ) (f : ι → ℝ) :
    let G : (ι → ℝ) → ℝ := fun g => ∑ i, w i * |g i| ^ p
    let F : (ι → ℝ) → ℝ := fun g =>
      ρ ^ (2 : ℕ) * (∑ i, w i * g i ^ (2 : ℕ)) +
        (1 - ρ ^ (2 : ℕ)) * (∑ i, w i * g i) ^ (2 : ℕ)
    G (fun i => t * f i) = |t| ^ p * G f ∧
      F (fun i => t * f i) = t ^ (2 : ℕ) * F f := by
  classical
  intro G F
  constructor
  · dsimp only [G]
    simp only [abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _),
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · dsimp only [F]
    calc
      ρ ^ (2 : ℕ) * (∑ i, w i * (t * f i) ^ (2 : ℕ)) +
          (1 - ρ ^ (2 : ℕ)) * (∑ i, w i * (t * f i)) ^ (2 : ℕ) =
        ρ ^ (2 : ℕ) * (∑ i, t ^ (2 : ℕ) * (w i * f i ^ (2 : ℕ))) +
          (1 - ρ ^ (2 : ℕ)) * (∑ i, t * (w i * f i)) ^ (2 : ℕ) := by
        congr 2
        · apply Finset.sum_congr rfl
          intro i _
          ring
        · congr 1
          apply Finset.sum_congr rfl
          intro i _
          ring
      _ = _ := by
        rw [← Finset.mul_sum, ← Finset.mul_sum, mul_pow]
        ring



/-- If real functions `f` and `g` have derivatives `a` and `b` at `x`,
`g x = 1`, and `t ↦ f t / g t ^ r` has a local maximum at `x`, then
`a = r * f x * b`.

This is the one-variable calculus identity used in [OD14, Exercise 10.19(d)-(f)].
The motivating finite-noise setting is extended to arbitrary differentiable
real functions and an arbitrary real exponent, without sign assumptions on
`f` or `r`. The normalization `g x = 1` suffices; no separate positivity
hypothesis on `g` away from `x` is required.

**Proof sketch.** Differentiate the real power of `g` and then the quotient.
At the normalized point the quotient derivative is `a - r * f x * b`.
A differentiable function has zero derivative at a local maximum, so
rearranging gives the asserted identity. -/
theorem derivative_eq_mul_of_isLocalMax_quotient
    (f g : ℝ → ℝ) (x r a b : ℝ)
    (hf : HasDerivAt f a x) (hg : HasDerivAt g b x)
    (hg_one : g x = 1)
    (hmax : IsLocalMax (fun t => f t / g t ^ r) x) :
    a = r * f x * b := by
  have hzero := hmax.hasDerivAt_eq_zero
    (hf.div (hg.rpow_const (p := r) (Or.inl (by simp [hg_one])))
      (by simp [hg_one]))
  simpa [hg_one, sub_eq_zero, mul_assoc, mul_left_comm, mul_comm] using hzero

/-- For a real-valued function on a finite type with positive weighted absolute
`p` moment and `p ≠ 0`, scaling by `c = G f ^ (-1 / p)` gives unit weighted
moment and divides the quadratic noise objective by `G f ^ (2 / p)`.

These are technical normalization identities used in [OD14, Exercise 10.19(a),
(c)–(e)], supporting [OD14, Theorem 10.18]. The source's positive normalized
weights, exponent range, and noise-radius range are extended to arbitrary real
weights, nonzero real exponents, and arbitrary real noise parameters:
positivity of the actual weighted moment and a nonzero exponent suffice.

**Proof sketch.** Positivity of the weighted moment makes the scaling factor
positive. Real-power identities and the nonzero exponent give
`c ^ p = 1 / G f` and `c² = 1 / G f ^ (2 / p)`.
Apply `finite_noise_homogeneity` with this scaling factor, replace its absolute
value by itself, and substitute these identities into the two scaling laws. -/
theorem finite_noise_normalization {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (p ρ : ℝ) (hp : p ≠ 0)
    (f : ι → ℝ) (hf : 0 < ∑ i, w i * |f i| ^ p) :
    let G : (ι → ℝ) → ℝ := fun g => ∑ i, w i * |g i| ^ p
    let F : (ι → ℝ) → ℝ := fun g =>
      ρ ^ (2 : ℕ) * (∑ i, w i * g i ^ (2 : ℕ)) +
        (1 - ρ ^ (2 : ℕ)) * (∑ i, w i * g i) ^ (2 : ℕ)
    let c : ℝ := G f ^ (-1 / p)
    G (fun i => c * f i) = 1 ∧
      F (fun i => c * f i) = F f / G f ^ (2 / p) := by
  classical
  intro G F c
  change 0 < G f at hf
  have hc : 0 < c := Real.rpow_pos_of_pos hf _
  obtain ⟨hG, hF⟩ := finite_noise_homogeneity w p ρ c f
  change G (fun i => c * f i) = |c| ^ p * G f at hG
  change F (fun i => c * f i) = c ^ (2 : ℕ) * F f at hF
  have hcp : c ^ p = (G f)⁻¹ := by
    dsimp only [c]
    rw [← Real.rpow_mul hf.le, div_mul_cancel₀ _ hp, Real.rpow_neg_one]
  have hc2 : c ^ (2 : ℕ) = (G f ^ (2 / p))⁻¹ := by
    dsimp only [c]
    rw [← Real.rpow_mul_natCast hf.le]
    norm_num only [Nat.cast_ofNat]
    rw [show (-1 / p) * (2 : ℝ) = -(2 / p) by ring, Real.rpow_neg hf.le]
  constructor
  · rw [hG, abs_of_pos hc, hcp, inv_mul_cancel₀ hf.ne']
  · rw [hF, hc2]
    simp only [div_eq_mul_inv, mul_comm]


/-- For a finite index type, arbitrary real weights `w`, an exponent `p > 1`,
an arbitrary real parameter `ρ`, a nonnegative function `g`, and an arbitrary
real direction `h`, the weighted absolute moment
`G f = ∑ i, w i * |f i| ^ p` and quadratic noise objective
`F f = ρ² * (∑ i, w i * f i²) + (1 - ρ²) * (∑ i, w i * f i)²`
have derivatives along `t ↦ g + t * h` at `t = 0` equal to
`p * (∑ i, w i * g i ^ (p - 1) * h i)` and
`2 * (ρ² * (∑ i, w i * g i * h i) +
(1 - ρ²) * (∑ i, w i * g i) * (∑ i, w i * h i))`, respectively.

This is the directional form of [OD14, Exercise 10.19(d)], used for the
stationary equation (10.33) in [OD14, Exercise 10.19(e)–(f)], supporting
[OD14, Theorem 10.18]. This technical extension permits weights that are
neither positive nor normalized, arbitrary `ρ`, and all `p > 1` rather
than only `1 < p < 2`: these additional source restrictions are unnecessary
for differentiability. Zero coordinates and an empty index type are included.

**Proof sketch.** Each affine coordinate has derivative `h i`. Compose this
with the derivative of the absolute real power, which exists even at zero
because `p > 1`. Nonnegativity of `g i` and the real-power multiplication
identity rewrite the coordinate derivative as `p * g i ^ (p - 1) * h i`,
including when `g i = 0`. Multiply by each weight and sum to obtain the
moment derivative. For the quadratic objective, differentiate each coordinate
square and the square of the weighted mean. Apply the finite-sum and
constant-multiplication rules and factor out two to obtain the stated formula. -/
theorem finite_noise_directional_derivatives {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (p ρ : ℝ) (hp : 1 < p)
    (g h : ι → ℝ) (hg : ∀ i, 0 ≤ g i) :
    let G : (ι → ℝ) → ℝ := fun f => ∑ i, w i * |f i| ^ p
    let F : (ι → ℝ) → ℝ := fun f =>
      ρ ^ (2 : ℕ) * (∑ i, w i * f i ^ (2 : ℕ)) +
        (1 - ρ ^ (2 : ℕ)) * (∑ i, w i * f i) ^ (2 : ℕ)
    HasDerivAt (fun t : ℝ => G (fun i => g i + t * h i))
      (p * (∑ i, w i * g i ^ (p - 1) * h i)) (0 : ℝ) ∧
    HasDerivAt (fun t : ℝ => F (fun i => g i + t * h i))
      (2 * (ρ ^ (2 : ℕ) * (∑ i, w i * g i * h i) +
        (1 - ρ ^ (2 : ℕ)) * (∑ i, w i * g i) * (∑ i, w i * h i)))
      (0 : ℝ) := by
  classical
  intro G F
  have haffine (i : ι) :
      HasDerivAt (fun t : ℝ => g i + t * h i) (h i) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (h i)).const_add (g i)
  have hmean :
      HasDerivAt (fun t : ℝ => ∑ i, w i * (g i + t * h i))
        (∑ i, w i * h i) 0 :=
    HasDerivAt.fun_sum fun i _ => (haffine i).const_mul (w i)
  have hsecond :
      HasDerivAt (fun t : ℝ => ∑ i, w i * (g i + t * h i) ^ (2 : ℕ))
        (2 * (∑ i, w i * g i * h i)) 0 := by
    convert HasDerivAt.fun_sum (u := Finset.univ)
      (fun i _ => ((haffine i).pow 2).const_mul (w i)) using 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [zero_mul, add_zero, Nat.cast_ofNat, Nat.reduceSub, pow_one]
    ring
  constructor
  · dsimp only [G]
    rw [Finset.mul_sum]
    apply HasDerivAt.fun_sum
    intro i _
    convert (((hasDerivAt_abs_rpow (g i) hp).comp_of_eq (0 : ℝ)
      (haffine i) (by simp)).const_mul (w i)) using 1
    rw [abs_of_nonneg (hg i), mul_assoc p (g i ^ (p - 2)) (g i),
      ← Real.rpow_add_one' (hg i) (by linarith),
      show p - 2 + 1 = p - 1 by ring]
    ring
  · dsimp only [F]
    convert (hsecond.const_mul (ρ ^ (2 : ℕ))).add
      ((hmean.pow 2).const_mul (1 - ρ ^ (2 : ℕ))) using 1
    simp only [zero_mul, add_zero, Nat.cast_ofNat, Nat.reduceSub, pow_one]
    ring

/-- A nonnegative unit-moment maximizer of the quadratic noise objective on a
finite probability space has objective value at least one and satisfies
`F g * g i ^ (p - 1) - ρ² * g i = (1 - ρ²) * ∑ j, w j * g j`
at every coordinate, for strictly positive normalized weights, `1 < p < 2`,
and `0 ≤ ρ < 1`.

This is the stationary equation (10.33) from [OD14, Exercise 10.19(d)–(f)],
supporting [OD14, Theorem 10.18]. It uses the exercise's maximization
formulation, correcting the min/max inconsistency in the ingested text.
Zero coordinates are permitted; no separate positivity or multiplier
hypothesis is assumed.
The range includes `ρ = 0`, since the same normalized variation argument applies
at that endpoint. The source's multiplier is identified explicitly as `F g`.

**Proof sketch.** First compare the maximizer with the constant-one function,
whose weighted moment and noise objective both equal one. For each coordinate,
perturb the maximizer in the direction that is one at that coordinate and zero
elsewhere. The computed moment derivative gives continuity at zero, so the
moment remains positive nearby. The normalization identities, obtained from
homogeneity, turn each nearby perturbation into a unit-moment function and
express its objective as the quotient of its original objective by its moment
raised to `2 / p`. Maximality therefore gives a local maximum of this quotient
at zero. Apply the generic quotient derivative equation and the directional
derivative formulas, valid also at zero coordinates because `p > 1`.
Cancel the positive coordinate weight and rearrange to obtain the stationary
equation. -/
theorem finite_noise_maximizer_stationarity {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (hw_sum : ∑ i, w i = 1)
    (p ρ : ℝ) (hp_one : 1 < p) (hp_two : p < 2)
    (hρ_nonneg : 0 ≤ ρ) (hρ_lt_one : ρ < 1)
    (g : ι → ℝ) (hg : ∀ i, 0 ≤ g i) :
    let G : (ι → ℝ) → ℝ := fun f => ∑ i, w i * |f i| ^ p
    let F : (ι → ℝ) → ℝ := fun f =>
      ρ ^ (2 : ℕ) * (∑ i, w i * f i ^ (2 : ℕ)) +
        (1 - ρ ^ (2 : ℕ)) * (∑ i, w i * f i) ^ (2 : ℕ)
    G g = 1 →
      (∀ f : ι → ℝ, G f = 1 → F f ≤ F g) →
      1 ≤ F g ∧
        ∀ i, F g * g i ^ (p - 1) - ρ ^ (2 : ℕ) * g i =
          (1 - ρ ^ (2 : ℕ)) * (∑ j, w j * g j) := by
  classical
  intro G F hunit hmax
  have p_nonzero : p ≠ 0 := ne_of_gt (lt_trans zero_lt_one hp_one)
  constructor
  · -- Compare with the admissible constant-one function.
    have hone : F (fun _ => 1) = 1 := by
      simp [F, hw_sum]
    simpa only [hone] using
      hmax (fun _ => 1) (by simpa [G] using hw_sum)
  · intro i
    let h : ι → ℝ := fun j => if j = i then 1 else 0
    let u : ℝ → ι → ℝ := fun t j => g j + t * h j
    obtain ⟨hG, hF⟩ :
        HasDerivAt (fun t : ℝ => G (u t))
          (p * (w i * g i ^ (p - 1))) 0 ∧
        HasDerivAt (fun t : ℝ => F (u t))
          (2 * (ρ ^ (2 : ℕ) * (w i * g i) +
            (1 - ρ ^ (2 : ℕ)) * (∑ j, w j * g j) * w i)) 0 := by
      simpa [u, h, mul_ite] using
        finite_noise_directional_derivatives w p ρ hp_one g h hg
    -- Nearby perturbations have positive moment and normalize to admissible functions.
    have hmoment_zero : G (u 0) = 1 := by
      simpa [u] using hunit
    have hpositive : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < G (u t) :=
      Filter.Tendsto.eventually_const_lt
        (by simpa [hmoment_zero] using (zero_lt_one : (0 : ℝ) < 1))
        hG.continuousAt
    have hquotient :
        IsLocalMax (fun t => F (u t) / G (u t) ^ (2 / p)) 0 := by
      change ∀ᶠ t in 𝓝 (0 : ℝ),
        F (u t) / G (u t) ^ (2 / p) ≤
          F (u 0) / G (u 0) ^ (2 / p)
      filter_upwards [hpositive] with t ht
      obtain ⟨hnorm, hvalue⟩ :=
        finite_noise_normalization w p ρ p_nonzero (u t) ht
      calc
        F (u t) / G (u t) ^ (2 / p) =
            F (fun j => G (u t) ^ (-1 / p) * u t j) := hvalue.symm
        _ ≤ F g := hmax _ hnorm
        _ = F (u 0) / G (u 0) ^ (2 / p) := by
          simp [u, hunit]
    -- Differentiate the quotient and cancel the nonzero coordinate weight.
    have heq := derivative_eq_mul_of_isLocalMax_quotient
      (fun t => F (u t)) (fun t => G (u t))
      0 (2 / p) _ _ hF hG hmoment_zero hquotient
    simp only [u, zero_mul, add_zero] at heq
    field_simp [p_nonzero] at heq
    apply mul_left_cancel₀ (hw i).ne'
    linear_combination -heq

/-- A nonnegative unit-moment maximizer of the quadratic noise objective on a
finite probability space takes at most two nonnegative values, for strictly
positive normalized weights, `1 < p < 2`, and `0 ≤ ρ < 1`.

This is the two-value reduction in [OD14, Exercise 10.19(e)–(g)], using the
stationary equation (10.33) and supporting [OD14, Theorem 10.18]. It follows
the maximization formulation documented in `finite_noise_maximizer_stationarity`.
Zero coordinates are included, and the two values may coincide.

**Proof sketch.** The stationary equation gives an objective value `C ≥ 1`
and a common value of `C * y ^ (p - 1) - ρ² * y` at all coordinates of the
maximizer. Divide by the positive constant `C` to obtain a common level set
of `y ↦ y ^ (p - 1) - (ρ² / C) * y`. Since `0 < p - 1 < 1`, the real-power
function is strictly concave on the whole nonnegative half-line. Subtracting
the convex linear function preserves strict concavity. Apply the finite
strictly concave level-set lemma to conclude that every coordinate equals
one of two nonnegative values. -/
theorem finite_noise_maximizer_two_values {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (hw_sum : ∑ i, w i = 1)
    (p ρ : ℝ) (hp_one : 1 < p) (hp_two : p < 2)
    (hρ_nonneg : 0 ≤ ρ) (hρ_lt_one : ρ < 1)
    (g : ι → ℝ) (hg : ∀ i, 0 ≤ g i) :
    let G : (ι → ℝ) → ℝ := fun f => ∑ i, w i * |f i| ^ p
    let F : (ι → ℝ) → ℝ := fun f =>
      ρ ^ (2 : ℕ) * (∑ i, w i * f i ^ (2 : ℕ)) +
        (1 - ρ ^ (2 : ℕ)) * (∑ i, w i * f i) ^ (2 : ℕ)
    G g = 1 →
      (∀ f : ι → ℝ, G f = 1 → F f ≤ F g) →
      ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ ∀ i, g i = a ∨ g i = b := by
  classical
  intro G F hunit hmax
  obtain ⟨hC, hstationary⟩ :=
    finite_noise_maximizer_stationarity w hw hw_sum p ρ hp_one hp_two
      hρ_nonneg hρ_lt_one g hg hunit hmax
  have hCpos : 0 < F g := lt_of_lt_of_le zero_lt_one hC
  have hconcave : StrictConcaveOn ℝ (Set.Ici 0)
      (fun y : ℝ => y ^ (p - 1) - (ρ ^ (2 : ℕ) / F g) * y) := by
    simpa only [Pi.sub_apply, smul_eq_mul, id_eq] using
      (Real.strictConcaveOn_rpow (p := p - 1)
        (by linarith) (by linarith)).sub_convexOn
        (ConvexOn.smul (div_nonneg (sq_nonneg ρ) hCpos.le)
          (convexOn_id (convex_Ici (0 : ℝ))))
  refine finite_concave_level_two_values _ hconcave g hg
    (((1 - ρ ^ (2 : ℕ)) * (∑ j, w j * g j)) / F g) ?_
  intro i
  field_simp [hCpos.ne']
  linear_combination hstationary i

end BooleanAnalysis.Hypercontractivity.SharpDiscrete
