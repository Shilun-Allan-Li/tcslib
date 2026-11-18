/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.SurfaceArea
import TCSlib.BooleanAnalysis.GaussianSpace.SurfaceExamples.Crossings
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Complex.BigOperators
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Gaussian surface area of polynomial thresholds

## Main definitions

Uses the existing multivariate polynomial evaluation and Gaussian rotation perimeter.

## Main results

* `polynomial_threshold_surfaceArea_bound`: the degree bound `k/√(2π)`.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.4, Example 11.50.
* [Kan11] D. Kane, The Gaussian surface area and noise sensitivity of degree-d
  polynomial threshold functions, Computational Complexity 20 (2011), 389–412, §2.
-/

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology
namespace BooleanAnalysis.GaussianSpace
open scoped BigOperators
open Polynomial
noncomputable section
namespace PolynomialCircle
variable {n k : ℕ}
/-- Homogenize the multivariate polynomial after substituting quadratic
univariate polynomials for its variables. The extra powers of `X` align degrees. -/
private def liftPoly (p : MvPolynomial (Fin n) ℝ) (A : Fin n → Polynomial ℂ) (k : ℕ) : Polynomial ℂ :=
  ∑ d ∈ p.support, C ((p.coeff d : ℝ) : ℂ) * X ^ (k - d.sum (fun _ e => e)) * ∏ i, A i ^ d i
/-- The homogenized polynomial has degree at most twice the original degree.

**Proof sketch.** Each monomial of degree `d ≤ k` contributes degree at most
`k - d + 2d ≤ 2k`; take the maximum over its finite support. -/
private lemma liftPoly_degree (p : MvPolynomial (Fin n) ℝ) (A : Fin n → Polynomial ℂ)
    (hp : p.totalDegree ≤ k) (hA : ∀ i, (A i).natDegree ≤ 2) :
    (liftPoly p A k).natDegree ≤ 2*k := by
  classical
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro d hd
  have hd' := (MvPolynomial.le_totalDegree hd).trans hp
  have hd'' : ∑ i, d i ≤ k := by
    simpa only [Finsupp.sum_fintype d (fun _ e => e) (by simp)] using hd'
  calc
    _ ≤ (C ((p.coeff d : ℝ) : ℂ) * X ^ (k-d.sum (fun _ e => e))).natDegree +
        (∏ i, A i ^ d i).natDegree := Polynomial.natDegree_mul_le
    _ ≤ (k-d.sum (fun _ e => e)) + ∑ i, 2*d i := by
      apply Nat.add_le_add
      · simpa using (Polynomial.natDegree_mul_le (p := C ((p.coeff d : ℝ) : ℂ))
          (q := X ^ (k-d.sum (fun _ e => e))))
      · apply (Polynomial.natDegree_prod_le _ _).trans
        apply Finset.sum_le_sum
        intro i hi
        exact (Polynomial.natDegree_pow_le).trans (by nlinarith [hA i])
    _ ≤ 2*k := by
      rw [Finsupp.sum_fintype d (fun _ e => e) (by simp), ← Finset.mul_sum]
      omega
/-- Substitutions evaluating to `z` times a vector coordinate make the lift
evaluate to `z^k` times the original multivariate polynomial.

**Proof sketch.** Expand over monomials, collect the powers of `z`, and use
the degree bound to cancel the homogenizing exponent. -/
private lemma liftPoly_eval (p : MvPolynomial (Fin n) ℝ) (A : Fin n → Polynomial ℂ)
    (hp : p.totalDegree ≤ k) (z : ℂ) (v : Fin n → ℝ)
    (hA : ∀ i, (A i).eval z = z * (v i : ℂ)) :
    (liftPoly p A k).eval z = z^k * (MvPolynomial.eval v p : ℂ) := by
  classical
  rw [MvPolynomial.eval_eq']
  simp only [liftPoly, Polynomial.eval_finset_sum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_prod,
    Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_prod, Complex.ofReal_pow,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hd' := (MvPolynomial.le_totalDegree hd).trans hp
  have hd'' : ∑ i, d i ≤ k := by
    simpa only [Finsupp.sum_fintype d (fun _ e => e) (by simp)] using hd'
  simp_rw [hA, mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    Finsupp.sum_fintype d (fun _ e => e) (by simp)]
  rw [← mul_assoc, mul_assoc ((p.coeff d : ℝ) : ℂ), ← pow_add,
    Nat.sub_add_cancel hd'']
  ring
/-- The quadratic encoding of one coordinate of a rotation circle. -/
private def circleQuad (x y : ℝ) : Polynomial ℂ :=
  C (((x:ℂ) - Complex.I*y)/2) * X^2 + C (((x:ℂ) + Complex.I*y)/2)
/-- Each coordinate encoding has degree at most two. -/
private lemma circleQuad_degree (x y : ℝ) : (circleQuad x y).natDegree ≤ 2 := by
  apply Polynomial.natDegree_add_le_of_degree_le
  · exact (Polynomial.natDegree_C_mul_le (((x:ℂ) - Complex.I*y)/2) (X^2)).trans
      (by rw [Polynomial.natDegree_X_pow])
  · simp
/-- On the unit circle, the quadratic equals the circle parameter times
the real rotated coordinate.

**Proof sketch.** Expand the quadratic and use `cos² t + sin² t = 1`. -/
private lemma circleQuad_eval (x y t : ℝ) :
    (circleQuad x y).eval ((Real.cos t : ℂ) + Complex.I*Real.sin t) =
      ((Real.cos t : ℂ) + Complex.I*Real.sin t) * ((Real.cos t*x + Real.sin t*y : ℝ) : ℂ) := by
  have hcs : (Real.cos t : ℂ)^2 + (Real.sin t : ℂ)^2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq t
  simp only [circleQuad, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    Complex.ofReal_add, Complex.ofReal_mul]
  linear_combination (norm := skip) -((x:ℂ) + Complex.I*y)/2 * hcs
  ring_nf
  simp only [Complex.I_sq, show Complex.I^3 = -Complex.I by rw [pow_succ, Complex.I_sq]; ring]
  ring
/-- Restricting a degree-`k` polynomial to a rotation circle yields a complex
polynomial of degree at most `2k`, up to a nonzero circle factor.
[OD14, Example 11.50; Kan11, §2]

**Proof sketch.** Use a quadratic for each coordinate, homogenize to degree `k`,
and apply the monomial evaluation identity. -/
private lemma exists_circlePoly (p : MvPolynomial (Fin n) ℝ)
    (hp : p.totalDegree ≤ k) (x y : Fin n → ℝ) :
    ∃ q : Polynomial ℂ, q.natDegree ≤ 2*k ∧
      ∀ t : ℝ, q.eval ((Real.cos t : ℂ) + Complex.I*Real.sin t) =
        ((Real.cos t : ℂ) + Complex.I*Real.sin t)^k *
          (MvPolynomial.eval (fun i => Real.cos t*x i + Real.sin t*y i) p : ℂ) := by
  refine ⟨liftPoly p (fun i => circleQuad (x i) (y i)) k,
    liftPoly_degree p _ hp (fun i => circleQuad_degree _ _), ?_⟩
  intro t
  exact liftPoly_eval p _ hp _ _ (fun i => circleQuad_eval _ _ _)
end PolynomialCircle
/-- A small positive shift preserves finitely many weak threshold labels as
strict threshold labels and makes every shifted sample nonzero.

**Proof sketch.** Choose the shift smaller than the magnitude of every negative
sample; nonnegative samples become positive. -/
private lemma finite_shift_signs (s : Finset ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ s,
      (0 ≤ x ↔ 0 < x + ε) ∧ x + ε ≠ 0 := by
  classical
  have hsmall : ∃ ε : ℝ, 0 < ε ∧
      ∀ x ∈ s, x < 0 → ε < -x := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1, by norm_num, by simp⟩
    | @insert a s ha ih =>
        obtain ⟨ε, hε, hs⟩ := ih
        by_cases hneg : a < 0
        · refine ⟨min ε (-a / 2), lt_min hε (by linarith), ?_⟩
          intro x hx hxneg
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact (min_le_right ε (-x / 2)).trans_lt (by linarith)
          · exact (min_le_left ε (-a / 2)).trans_lt (hs x hx hxneg)
        · refine ⟨ε, hε, ?_⟩
          intro x hx hxneg
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact (hneg hxneg).elim
          · exact hs x hx hxneg
  obtain ⟨ε, hε, hs⟩ := hsmall
  refine ⟨ε, hε, ?_⟩
  intro x hx
  by_cases hnonneg : 0 ≤ x
  · have hpos : 0 < x + ε := by linarith
    exact ⟨iff_of_true hnonneg hpos, ne_of_gt hpos⟩
  · have hneg : x < 0 := lt_of_not_ge hnonneg
    have hshift : x + ε < 0 := by
      have := hs x hx hneg
      linarith
    exact ⟨iff_of_false hnonneg (not_lt_of_ge hshift.le), ne_of_lt hshift⟩
/-- Opposite nonzero endpoint signs force an interior zero by continuity. -/
private lemma zero_between_of_sign_change {f : ℝ → ℝ}
    (hf : Continuous f) {a b : ℝ} (hab : a < b)
    (ha : f a ≠ 0) (hb : f b ≠ 0)
    (hc : ¬ (0 ≤ f a ↔ 0 ≤ f b)) :
    ∃ t ∈ Set.Ioo a b, f t = 0 := by
  by_cases hfa : 0 ≤ f a
  · have hfb : f b < 0 := by
      by_contra h
      exact hc (iff_of_true hfa (le_of_not_gt h))
    have hfa' : 0 < f a := lt_of_le_of_ne hfa ha.symm
    exact intermediate_value_Ioo' hab.le hf.continuousOn ⟨hfb, hfa'⟩
  · have hfb : 0 ≤ f b := by
      by_contra h
      exact hc (iff_of_false hfa h)
    have hfb' : 0 < f b := lt_of_le_of_ne hfb hb.symm
    exact intermediate_value_Ioo hab.le hf.continuousOn ⟨lt_of_not_ge hfa, hfb'⟩
/-- Sampled sign changes inject into the roots of a polynomial that encodes
the continuous function along an injective parametrization.

**Proof sketch.** The intermediate value theorem supplies a root inside each
changed interval. These intervals are disjoint, and the parametrization is
injective, so the roots are distinct. Their number is bounded by the degree. -/
private lemma sample_transitions_le_roots
    (N : ℕ) (a : ℕ → ℝ) (ha : StrictMono a)
    (f : ℝ → ℝ) (hf : Continuous f)
    (hsample : ∀ i ≤ N, f (a i) ≠ 0)
    (q : Polynomial ℂ) (hq : q ≠ 0)
    (z : ℝ → ℂ) (hz : Set.InjOn z (Set.Ioo (a 0) (a N)))
    (hroot : ∀ t ∈ Set.Ioo (a 0) (a N), f t = 0 → q.IsRoot (z t)) :
    ((Finset.range N).filter
      (fun i => ¬ (0 ≤ f (a i) ↔ 0 ≤ f (a (i + 1))))).card ≤ q.natDegree := by
  classical
  let s := (Finset.range N).filter
    (fun i => ¬ (0 ≤ f (a i) ↔ 0 ≤ f (a (i + 1))))
  have hw : ∀ i ∈ s,
      ∃ t, t ∈ Set.Ioo (a i) (a (i + 1)) ∧ q.IsRoot (z t) := by
    intro i hi
    obtain ⟨hiN, hchange⟩ := Finset.mem_filter.mp hi
    have hiN : i < N := Finset.mem_range.mp hiN
    obtain ⟨t, ht, hzero⟩ := zero_between_of_sign_change hf
      (ha (Nat.lt_succ_self i))
      (hsample i (by omega)) (hsample (i + 1) (by omega)) hchange
    refine ⟨t, ht, hroot t ?_ hzero⟩
    exact ⟨(ha.monotone (Nat.zero_le i)).trans_lt ht.1,
      ht.2.trans_le (ha.monotone (by omega))⟩
  let r : ℕ → ℝ := fun i => if hi : i ∈ s then Classical.choose (hw i hi) else 0
  have hr : ∀ i (hi : i ∈ s),
      r i ∈ Set.Ioo (a i) (a (i + 1)) ∧ q.IsRoot (z (r i)) := by
    intro i hi
    dsimp only [r]
    rw [dif_pos hi]
    exact Classical.choose_spec (hw i hi)
  have hglobal : ∀ i ∈ s, r i ∈ Set.Ioo (a 0) (a N) := by
    intro i hi
    have hiN : i < N := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    exact ⟨(ha.monotone (Nat.zero_le i)).trans_lt (hr i hi).1.1,
      (hr i hi).1.2.trans_le (ha.monotone (by omega))⟩
  have hcard : s.card ≤ q.roots.toFinset.card := by
    apply Finset.card_le_card_of_injOn (fun i => z (r i))
    · intro i hi
      exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hq).mpr (hr i hi).2)
    · intro i hi j hj heq
      have heq' : r i = r j := hz (hglobal i hi) (hglobal j hj) heq
      by_contra hne
      rcases lt_or_gt_of_ne hne with hij | hji
      · have horder : a (i + 1) ≤ a j := ha.monotone (by omega)
        have hiupper := (hr i hi).1.2
        have hjlower := (hr j hj).1.1
        linarith
      · have horder : a (j + 1) ≤ a i := ha.monotone (by omega)
        have hjupper := (hr j hj).1.2
        have hilower := (hr i hi).1.1
        linarith
  exact hcard.trans ((Multiset.toFinset_card_le q.roots).trans (Polynomial.card_roots' q))
/-- Circle parametrization is injective inside an arc of length at most `2π`. -/
private lemma circleMap_injOn_Ioo {a b : ℝ} (hab : b - a ≤ 2 * Real.pi) :
    Set.InjOn (circleMap 0 1) (Set.Ioo a b) := by
  intro x hx y hy he
  apply injOn_circleMap_of_abs_sub_le' (c := (0 : ℂ)) (R := (1 : ℝ))
    one_ne_zero hab (show x ∈ Set.Ico a b from ⟨hx.1.le, hx.2⟩)
    (show y ∈ Set.Ico a b from ⟨hy.1.le, hy.2⟩) he
/-- A polynomial threshold changes its label at most twice its degree along
samples lying strictly within one full rotation. [OD14, Example 11.50; Kan11, §2]

**Proof sketch.** Slightly shift the polynomial so that no sampled value is zero
while preserving all threshold labels. Encode its circle restriction as a
complex polynomial of degree at most `2k`. Every change supplies a distinct
root in an open interval, so the polynomial root bound finishes the count. -/
private lemma polynomial_circle_changes_le {n k : ℕ}
    (p : MvPolynomial (Fin n) ℝ) (hp : p.totalDegree ≤ k)
    (x y : Fin n → ℝ) (N : ℕ) :
    ((Finset.range N).filter (fun (j : ℕ) =>
      ¬ ((0 ≤ MvPolynomial.eval
          (fun i => Real.cos ((j : ℝ) * (2 * Real.pi / (N + 1))) * x i +
            Real.sin ((j : ℝ) * (2 * Real.pi / (N + 1))) * y i) p) ↔
        (0 ≤ MvPolynomial.eval
          (fun i => Real.cos (((j + 1 : ℕ) : ℝ) * (2 * Real.pi / (N + 1))) * x i +
            Real.sin (((j + 1 : ℕ) : ℝ) * (2 * Real.pi / (N + 1))) * y i) p)))).card
      ≤ 2 * k := by
  classical
  let δ : ℝ := 2 * Real.pi / (N + 1)
  let a : ℕ → ℝ := fun j => (j : ℝ) * δ
  let f : ℝ → ℝ := fun t =>
    MvPolynomial.eval (fun i => Real.cos t * x i + Real.sin t * y i) p
  have hδ : 0 < δ := div_pos (by positivity) (by positivity)
  have ha : StrictMono a := by
    intro i j hij
    exact mul_lt_mul_of_pos_right (by exact_mod_cast hij) hδ
  obtain ⟨ε, hε, hs⟩ := finite_shift_signs
    ((Finset.range (N + 1)).image (fun j => f (a j)))
  have hs' (j : ℕ) (hj : j ≤ N) :
      (0 ≤ f (a j) ↔ 0 < f (a j) + ε) ∧ f (a j) + ε ≠ 0 :=
    hs _ (Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (by omega), rfl⟩)
  let g : ℝ → ℝ := fun t => f t + ε
  have hg : Continuous g := by
    apply Continuous.add _ continuous_const
    exact (MvPolynomial.continuous_eval p).comp
      (continuous_pi fun i =>
        (Real.continuous_cos.mul continuous_const).add
          (Real.continuous_sin.mul continuous_const))
  have hsample (j : ℕ) (hj : j ≤ N) : g (a j) ≠ 0 := (hs' j hj).2
  have hsign (j : ℕ) (hj : j ≤ N) : 0 ≤ g (a j) ↔ 0 ≤ f (a j) := by
    constructor
    · intro h
      exact (hs' j hj).1.mpr (lt_of_le_of_ne h (hsample j hj).symm)
    · intro h
      exact ((hs' j hj).1.mp h).le
  let pε : MvPolynomial (Fin n) ℝ := p + MvPolynomial.C ε
  have hpε : pε.totalDegree ≤ k :=
    (MvPolynomial.totalDegree_add _ _).trans (max_le hp (by simp))
  obtain ⟨q, hdegree, heval⟩ := PolynomialCircle.exists_circlePoly pε hpε x y
  have heval' (t : ℝ) :
      q.eval ((Real.cos t : ℂ) + Complex.I * Real.sin t) =
        ((Real.cos t : ℂ) + Complex.I * Real.sin t) ^ k * (g t : ℂ) := by
    simpa only [pε, MvPolynomial.eval_add, MvPolynomial.eval_C,
      Complex.ofReal_add, g, f] using heval t
  have hq : q ≠ 0 := by
    intro hzero
    have hq0 : q.eval 1 = (g 0 : ℂ) := by simpa using heval' 0
    have hg0 : g 0 ≠ 0 := by
      simpa only [a, Nat.cast_zero, zero_mul] using hsample 0 (Nat.zero_le N)
    apply hg0
    have : (g 0 : ℂ) = 0 := by
      rw [← hq0, hzero]
      simp
    exact_mod_cast this
  have hcircle (t : ℝ) :
      circleMap (0 : ℂ) (1 : ℝ) t = (Real.cos t : ℂ) + Complex.I * Real.sin t := by
    rw [circleMap_zero]
    simp only [Complex.ofReal_one, one_mul, Complex.exp_mul_I,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    ring
  have harc : a N - a 0 ≤ 2 * Real.pi := by
    dsimp only [a]
    simp only [Nat.cast_zero, zero_mul, sub_zero]
    have hN : (N : ℝ) ≤ N + 1 := by linarith
    calc
      (N : ℝ) * δ ≤ (N + 1) * δ := mul_le_mul_of_nonneg_right hN hδ.le
      _ = 2 * Real.pi := by dsimp only [δ]; field_simp
  have hcount := sample_transitions_le_roots N a ha g hg hsample
    q hq (circleMap 0 1) (circleMap_injOn_Ioo harc) (by
      intro t ht hzero
      change q.eval (circleMap 0 1 t) = 0
      rw [hcircle, heval', hzero]
      simp)
  have hfilters :
      ((Finset.range N).filter (fun j => ¬ (0 ≤ f (a j) ↔ 0 ≤ f (a (j + 1))))) =
      ((Finset.range N).filter (fun j => ¬ (0 ≤ g (a j) ↔ 0 ≤ g (a (j + 1))))) := by
    apply Finset.filter_congr
    intro j hj
    have hjN := Finset.mem_range.mp hj
    rw [hsign j (by omega), hsign (j + 1) (by omega)]
  have hfinal :
      ((Finset.range N).filter (fun j => ¬ (0 ≤ f (a j) ↔ 0 ≤ f (a (j + 1))))).card ≤ 2 * k := by
    rw [hfilters]
    exact hcount.trans hdegree
  exact hfinal
/-- The rotation crossing constant equals the stated Gaussian density constant. -/
private lemma polynomial_crossing_normalization (k : ℕ) :
    Real.sqrt (Real.pi / 2) * (k:ℝ) / Real.pi =
      (k:ℝ) / Real.sqrt (2 * Real.pi) := by
  have hpi := Real.pi_pos
  have hs := Real.sqrt_pos.2 (show 0 < 2 * Real.pi by positivity)
  have hp := Real.sq_sqrt (show 0 ≤ Real.pi / 2 by positivity)
  have hq := Real.sq_sqrt (show 0 ≤ 2 * Real.pi by positivity)
  have he : Real.sqrt (Real.pi / 2) * Real.sqrt (2 * Real.pi) = Real.pi := by
    rw [← Real.sqrt_mul (by positivity)]
    rw [show Real.pi / 2 * (2 * Real.pi) = Real.pi ^ 2 by ring]
    exact Real.sqrt_sq hpi.le
  apply (div_eq_div_iff (ne_of_gt hpi) (ne_of_gt hs)).2
  nlinarith [he]

/-- A bound of `2k` on expected changes before a full turn gives surface area
at most `k/√(2π)`. [OD14, Example 11.50; Kan11, §2]

**Proof sketch.** Divide the crossing bound by the step length `2π/(N+1)`.
The resulting upper bound is the claimed constant times `(N+1)/N`. Let `N`
tend to infinity and use the surface-area rotation limit. -/
private lemma polynomial_surfaceArea_of_crossings {n k : ℕ} {A : Set (Fin n → ℝ)}
    (hA : MeasurableSet A)
    (h : ∀ N : ℕ, (N:ℝ) * rotationSensitivity A (2 * Real.pi / ((N:ℝ)+1)) ≤ 2*k) :
    gaussianSurfaceArea A ≤ ENNReal.ofReal ((k:ℝ)/Real.sqrt (2*Real.pi)) := by
  let C := Real.sqrt (Real.pi/2) * (k:ℝ) / Real.pi
  have ht : Tendsto (fun N : ℕ => 2*Real.pi / ((N:ℝ)+1)) atTop (𝓝[>] (0:ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, Eventually.of_forall (fun N => ?_)⟩
    · simpa only [mul_one_div, mul_zero] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2*Real.pi)
    · change 0 < 2*Real.pi / ((N:ℝ)+1)
      positivity
  have hr : Tendsto (fun N : ℕ => ((N:ℝ)+1)/(N:ℝ)) atTop (𝓝 (1:ℝ)) := by
    simpa [add_comm] using tendsto_add_mul_div_add_mul_atTop_nhds
      (1:ℝ) 0 1 (d:=1) (by norm_num)
  have hu : Tendsto (fun N : ℕ => ENNReal.ofReal (C * (((N:ℝ)+1)/(N:ℝ))))
      atTop (𝓝 (ENNReal.ofReal C)) := by
    simpa only [mul_one] using (ENNReal.continuous_ofReal.tendsto C).comp (by simpa only [mul_one] using hr.const_mul C)
  have hh : gaussianSurfaceArea A ≤ ENNReal.ofReal C := by
    apply le_of_tendsto_of_tendsto ((surfaceArea_rotation_limit hA).comp ht) hu
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hNp : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hdp : 0 < 2*Real.pi / ((N:ℝ)+1) := by positivity
    apply ENNReal.ofReal_le_ofReal
    apply (div_le_iff₀ hdp).2
    have hb : rotationSensitivity A (2*Real.pi / ((N:ℝ)+1)) ≤ 2*k/(N:ℝ) :=
      (le_div_iff₀ hNp).2 (by simpa [mul_comm] using h N)
    calc
      Real.sqrt (Real.pi/2) * rotationSensitivity A (2*Real.pi / ((N:ℝ)+1)) ≤
          Real.sqrt (Real.pi/2) * (2*k/(N:ℝ)) :=
        mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg _)
      _ = C * (((N:ℝ)+1)/(N:ℝ)) * (2*Real.pi / ((N:ℝ)+1)) := by
        dsimp [C]
        field_simp
  simpa only [C, polynomial_crossing_normalization] using hh
/-- A real polynomial threshold of degree at most `k` has Gaussian surface
area at most `k/√(2π)`, including arbitrary powers and the zero polynomial.
[OD14, Example 11.50; Kan11, §2]

**Proof sketch.** A circle restriction has at most `2k` sampled label changes.
Average over independent Gaussian vectors, using rotation invariance to give
each step the same crossing probability. Pass to the infinitesimal rotation
limit to obtain the stated surface-area bound. -/
theorem polynomial_threshold_surfaceArea_bound {n k : ℕ}
    (p : MvPolynomial (Fin n) ℝ) (hp : p.totalDegree ≤ k) :
    gaussianSurfaceArea {x : Fin n → ℝ | 0 ≤ MvPolynomial.eval x p} ≤
      ENNReal.ofReal ((k:ℝ) / Real.sqrt (2 * Real.pi)) := (by
  classical
    have hA : MeasurableSet {x : Fin n → ℝ | 0 ≤ MvPolynomial.eval x p} :=
      (isClosed_le continuous_const (MvPolynomial.continuous_eval p)).measurableSet
    apply polynomial_surfaceArea_of_crossings hA
    intro N
    apply rotationSensitivity_mul_nat_le_of_crossings _ hA N _ (2*k)
    intro x y
    rw [Finset.sum_boole]
    exact_mod_cast polynomial_circle_changes_le p hp x y N
)

end
end BooleanAnalysis.GaussianSpace
