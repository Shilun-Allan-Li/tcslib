/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/
import TCSlib.BooleanAnalysis.Hypercontractivity.RandomVariables.Sharp.FiniteNoiseOptimization
import TCSlib.BooleanAnalysis.Hypercontractivity.RandomVariables.Sharp.TwoPointContraction
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Finite-space grouping and noise contraction

This module groups two-valued finite functions and proves the sharp
finite-space conjugate noise contraction through the optimizer reduction.

## Main definitions

No new global definitions are introduced. Fiber masses are local expressions.

## Main results

* `finite_two_value_sum`: a weighted sum of any function of a two-valued
  finite function reduces to the two fiber contributions.
* `finite_two_value_mass_dichotomy`: either the function is constant or both
  value groups satisfy the atom lower bound.
* `finite_noise_contraction_of_unit_bound`: a unit-moment noise bound extends
  to arbitrary inputs by homogeneity, including zero.
* `finite_noise_sharp_contraction`: the full sharp conjugate noise bound for
  finite probability weights satisfying the atom lower bound.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014, §8.1, Exercises 10.18–10.20, and Theorem 10.18.
-/

open scoped BigOperators Classical

namespace BooleanAnalysis.Hypercontractivity.SharpDiscrete

/-- If a real-valued function on a finite type takes only the values `a` and `b`,
and real weights sum to one, then the weighted sum of any real function `φ`
of its values equals `gamma * φ a + (1 - gamma) * φ b`, where `gamma` is the
total weight of the fiber at `a`. The values may coincide.

This is a technical finite-sum specialization of [OD14, §8.1], used in the
two-value optimizer reduction of [OD14, Exercise 10.19] for
[OD14, Theorem 10.18]. It extends probability weights to arbitrary signed
real weights because the identity requires only their sum to equal one.
No positivity, regularity, or power assumptions on `φ` are imposed.

**Proof sketch.** Partition the index set into the fiber at `a` and its
complement. On the complement, the two-value hypothesis forces the value
to equal `b`. The two fiber weights sum to one, so the complement has weight
`1 - gamma`. Factor the constant function value from each sum to obtain the
identity. This disjoint partition also covers `a = b`. -/
theorem finite_two_value_sum {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw_sum : ∑ i, w i = 1)
    (f : ι → ℝ) (a b : ℝ) (hf : ∀ i, f i = a ∨ f i = b)
    (φ : ℝ → ℝ) :
    let gamma : ℝ := ∑ i ∈ Finset.univ.filter (fun i => f i = a), w i
    (∑ i, w i * φ (f i)) = gamma * φ a + (1 - gamma) * φ b := by
  classical
  intro gamma
  have hmass :
      (∑ i ∈ Finset.univ.filter (fun i => f i ≠ a), w i) = 1 - gamma := by
    have hpartition :=
      (Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => f i = a) w).trans
        hw_sum
    change gamma + (∑ i ∈ Finset.univ.filter (fun i => f i ≠ a), w i) = 1
      at hpartition
    exact eq_sub_of_add_eq' hpartition
  calc
    (∑ i, w i * φ (f i)) =
        ∑ i, if f i = a then w i * φ a else w i * φ b := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : f i = a
      · simp [hi]
      · rw [if_neg hi, (hf i).resolve_left hi]
    _ = gamma * φ a + (1 - gamma) * φ b := by
      rw [Finset.sum_ite, ← Finset.sum_mul, ← Finset.sum_mul, hmass]

/-- For a finite two-valued function with strictly positive weights summing
to one, each weight at least a positive `lam`, either the function is
constantly `a`, it is constantly `b`, or the total weight `gamma` of its
fiber at `a` satisfies `lam ≤ gamma ≤ 1 - lam`.

This is a technical grouping fact for the finite-space two-value reduction
in [OD14, Exercise 10.19(g)], supporting [OD14, Theorem 10.18].
Coincident values and constant functions are included, and no nonempty
index-type hypothesis is required.

**Proof sketch.** If either constant alternative holds, use it directly.
Otherwise, failure of constancy at `b` provides an index in the fiber at
`a`, and failure of constancy at `a` provides an index in its complement.
Each of these disjoint sets has total weight at least its witness's weight,
hence at least `lam`, because all weights are nonnegative. Their weights
sum to one, giving the lower and upper bounds on `gamma`. -/
theorem finite_two_value_mass_dichotomy {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (hw_sum : ∑ i, w i = 1)
    (lam : ℝ) (hlam_pos : 0 < lam) (hlam_le : ∀ i, lam ≤ w i)
    (f : ι → ℝ) (a b : ℝ) (hf : ∀ i, f i = a ∨ f i = b) :
    let gamma : ℝ := ∑ i ∈ Finset.univ.filter (fun i => f i = a), w i
    (∀ i, f i = a) ∨ (∀ i, f i = b) ∨
      (lam ≤ gamma ∧ gamma ≤ 1 - lam) := by
  classical
  intro gamma
  by_cases ha : ∀ i, f i = a
  · exact Or.inl ha
  by_cases hb : ∀ i, f i = b
  · exact Or.inr (Or.inl hb)
  obtain ⟨i, hi⟩ := not_forall.mp hb
  obtain ⟨j, hj⟩ := not_forall.mp ha
  have hmass :
      (∑ k ∈ Finset.univ.filter (fun k => f k ≠ a), w k) = 1 - gamma := by
    have hpartition :=
      (Finset.sum_filter_add_sum_filter_not Finset.univ (fun k => f k = a) w).trans
        hw_sum
    change gamma + (∑ k ∈ Finset.univ.filter (fun k => f k ≠ a), w k) = 1
      at hpartition
    exact eq_sub_of_add_eq' hpartition
  refine Or.inr (Or.inr ⟨?_, ?_⟩)
  · exact (hlam_le i).trans
      (Finset.single_le_sum (fun k _ => (hw k).le)
        (Finset.mem_filter.mpr
          ⟨Finset.mem_univ i, (hf i).resolve_right hi⟩))
  · apply le_sub_comm.mp
    rw [← hmass]
    exact (hlam_le j).trans
      (Finset.single_le_sum (fun k _ => (hw k).le)
        (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩))

/-- For a finite type, strictly positive real weights, a positive exponent `p`,
and any real noise parameter `ρ`, a bound `F f ≤ 1` on the unit weighted
absolute-moment level set implies `F f ≤ (G f) ^ (2 / p)` for every real
function `f`, where `G` is the weighted absolute `p` moment and `F` is the
quadratic noise objective.

This is a technical homogeneous extension of the unit-sphere reduction in
[OD14, Exercise 10.19(a)–(c)], supporting [OD14, Theorem 10.18].
For this implication, the weights need not sum to one, the exponent may be
any positive real number, and `ρ` may be arbitrary. Zero functions and an
empty index type are included.

**Proof sketch.** All weighted moment summands are nonnegative. If the moment
vanishes, every summand vanishes; positivity of the weights and exponent
forces every function value to be zero. The objective then vanishes and the
right-hand side is nonnegative. Otherwise, apply the normalization identities to scale
the function to unit moment. The assumed bound gives
`F f / (G f) ^ (2 / p) ≤ 1`. Multiplying by the positive denominator yields
the full inequality. -/
theorem finite_noise_contraction_of_unit_bound {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (p ρ : ℝ) (hp : 0 < p) :
    let G : (ι → ℝ) → ℝ := fun f => ∑ i, w i * |f i| ^ p
    let F : (ι → ℝ) → ℝ := fun f =>
      ρ ^ (2 : ℕ) * (∑ i, w i * f i ^ (2 : ℕ)) +
        (1 - ρ ^ (2 : ℕ)) * (∑ i, w i * f i) ^ (2 : ℕ)
    (∀ f : ι → ℝ, G f = 1 → F f ≤ 1) →
      ∀ f : ι → ℝ, F f ≤ G f ^ (2 / p) := by
  classical
  intro G F hunit f
  have hnonneg (i : ι) : 0 ≤ w i * |f i| ^ p :=
    mul_nonneg (hw i).le (Real.rpow_nonneg (abs_nonneg _) _)
  have hG : 0 ≤ G f := Finset.sum_nonneg (fun i _ => hnonneg i)
  rcases eq_or_lt_of_le hG with hzero | hpos
  · have hcoord : ∀ i, f i = 0 := by
      have hsummands :=
        (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
          (fun i _ => hnonneg i)).1 hzero.symm
      intro i
      exact abs_eq_zero.mp
        ((Real.rpow_eq_zero (abs_nonneg _) hp.ne').mp
          ((mul_eq_zero.mp (hsummands i (Finset.mem_univ i))).resolve_left
            (hw i).ne'))
    simpa [F, hcoord] using Real.rpow_nonneg hG (2 / p)
  · obtain ⟨hnorm, hvalue⟩ :=
      finite_noise_normalization w p ρ hp.ne' f hpos
    apply (div_le_one (Real.rpow_pos_of_pos hpos _)).1
    rw [← hvalue]
    exact hunit _ hnorm

/-- For `q > 2`, `0 < lam < 1 / 2`, and finite real weights summing to one
with every weight at least `lam`, the quadratic noise objective at the sharp
discrete radius is bounded by the squared weighted `Lᵖ` norm of every real
function, where `p = q / (q - 1)`.

This is the finite-space conjugate contraction in [OD14, Theorem 10.18],
using the optimizer reduction in [OD14, Exercise 10.19] and the two-point
inequality in [OD14, Exercise 10.20]. The formulation allows `lam` to be
a lower bound for every atom; [OD14, Exercise 10.18(a)] supplies the
corresponding radius comparison. Weight positivity follows from this atom
bound, and no separate nonempty index-type hypothesis is needed.

**Proof sketch.** Derive positive weights and reduce by homogeneity to the
unit weighted `p`-moment level set. Its noise objective has a nonnegative
maximizer, which takes at most two values. If the maximizer is constant,
its nonnegativity and unit moment force its value to be one, giving objective
one. Otherwise, both value groups have masses between `lam` and `1 - lam`.
Apply the same two-value sum identity to its first, second, and absolute
`p` moments. The objective becomes the squared grouped mean plus the squared
radius times the grouped variance. The scalar inequality with the atom
lower bound makes this at most one. Maximality bounds every unit-moment
function, and the homogeneous extension yields the full inequality,
including zero inputs. -/
theorem finite_noise_sharp_contraction {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw_sum : ∑ i, w i = 1)
    (q lam : ℝ) (hq : 2 < q)
    (hlam_pos : 0 < lam) (hlam_lt_half : lam < 1 / 2)
    (hlam_le : ∀ i, lam ≤ w i) :
    let p : ℝ := q / (q - 1)
    let rho : ℝ := sharpDiscreteRadius q lam
    ∀ f : ι → ℝ,
      rho ^ (2 : ℕ) * (∑ i, w i * f i ^ (2 : ℕ)) +
          (1 - rho ^ (2 : ℕ)) * (∑ i, w i * f i) ^ (2 : ℕ) ≤
        (∑ i, w i * |f i| ^ p) ^ (2 / p) := by
  classical
  intro p rho
  let G : (ι → ℝ) → ℝ := fun f => ∑ i, w i * |f i| ^ p
  let F : (ι → ℝ) → ℝ := fun f =>
    rho ^ (2 : ℕ) * (∑ i, w i * f i ^ (2 : ℕ)) +
      (1 - rho ^ (2 : ℕ)) * (∑ i, w i * f i) ^ (2 : ℕ)
  change ∀ f, F f ≤ G f ^ (2 / p)
  have hw (i : ι) : 0 < w i := lt_of_lt_of_le hlam_pos (hlam_le i)
  have hconj : Real.HolderConjugate q p :=
    (Real.holderConjugate_iff_eq_conjExponent (by linarith : 1 < q)).2 rfl
  have hp_two : p < 2 := by
    dsimp only [p]
    apply (div_lt_iff₀ (by linarith : 0 < q - 1)).2
    linarith
  obtain ⟨hrho_pos, hrho_lt⟩ := radius_pos_lt_one q lam hq hlam_pos hlam_lt_half
  -- Homogeneity reduces the claim to unit-moment inputs.
  apply finite_noise_contraction_of_unit_bound w hw p rho hconj.symm.pos
  intro f hfunit
  obtain ⟨g, hg, hgunit, hmax⟩ :=
    exists_nonnegative_noise_maximizer w hw hw_sum p rho
      hconj.symm.lt hp_two hrho_pos.le hrho_lt.le
  refine (hmax f hfunit).trans ?_
  obtain ⟨a, b, ha, hb, hvalues⟩ :=
    finite_noise_maximizer_two_values w hw hw_sum p rho
      hconj.symm.lt hp_two hrho_pos.le hrho_lt g hg hgunit hmax
  -- A nonnegative constant maximizer has value one.
  have hconstant (c : ℝ) (hc : 0 ≤ c) (hgc : ∀ i, g i = c) : F g ≤ 1 := by
    have hc_one : c = 1 := by
      apply (Real.rpow_left_inj hc zero_le_one hconj.symm.ne_zero).1
      simpa only [G, hgc, abs_of_nonneg hc, ← Finset.sum_mul,
        hw_sum, one_mul, Real.one_rpow] using hgunit
    simp [F, hgc, hc_one, hw_sum]
  let gamma : ℝ := ∑ i ∈ Finset.univ.filter (fun i => g i = a), w i
  rcases finite_two_value_mass_dichotomy w hw hw_sum lam hlam_pos hlam_le
      g a b hvalues with hga | hgb | ⟨hgamma_lower, hgamma_upper⟩
  · exact hconstant a ha hga
  · exact hconstant b hb hgb
  · -- Group the three moments and apply the scalar atom-bound inequality.
    have hgroup (φ : ℝ → ℝ) :
        (∑ i, w i * φ (g i)) = gamma * φ a + (1 - gamma) * φ b :=
      finite_two_value_sum w hw_sum g a b hvalues φ
    have hmoment : gamma * |a| ^ p + (1 - gamma) * |b| ^ p = 1 := by
      rw [← hgroup (fun x => |x| ^ p)]
      exact hgunit
    have hscalar := weighted_two_point_le_of_atom_bound q lam gamma a b
      hq hlam_pos hlam_lt_half hgamma_lower hgamma_upper
    change (gamma * a + (1 - gamma) * b) ^ (2 : ℕ) +
        rho ^ (2 : ℕ) * gamma * (1 - gamma) * (a - b) ^ (2 : ℕ) ≤
      (gamma * |a| ^ p + (1 - gamma) * |b| ^ p) ^ (2 / p) at hscalar
    calc
      F g = (gamma * a + (1 - gamma) * b) ^ (2 : ℕ) +
          rho ^ (2 : ℕ) * gamma * (1 - gamma) * (a - b) ^ (2 : ℕ) := by
        dsimp only [F]
        rw [hgroup (fun x => x ^ (2 : ℕ)), hgroup (fun x => x)]
        ring
      _ ≤ 1 := by
        simpa only [hmoment, Real.one_rpow] using hscalar


end BooleanAnalysis.Hypercontractivity.SharpDiscrete
