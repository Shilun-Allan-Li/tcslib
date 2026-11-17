/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.SurfaceExamples.Intervals
import Mathlib.Algebra.MvPolynomial.Degrees

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Polynomial thresholds approaching the Gaussian surface-area bound

Coordinate threshold polynomials with distinct roots near zero approach the
linear degree bound for Gaussian surface area.

## Main definitions

No new definitions are introduced.

## Main results

* `interval_threshold_polynomial`: polynomial representation of disjoint intervals.
* `interval_threshold_polynomial_extra_root`: representation with an additional ray.
* `exists_coordinate_polynomial_threshold_surfaceArea_ge`: sharpness in any
  ambient dimension with a specified coordinate.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University
  Press, 2014; May 2021 arXiv edition, §11.4, Example 11.50 and Exercise 11.16.
* [Kan11] D. Kane, The Gaussian surface area and noise sensitivity of degree-d
  polynomial threshold functions, Computational Complexity 20 (2011), 389–412.
-/

open MeasureTheory Filter
open scoped BigOperators Topology
namespace BooleanAnalysis.GaussianSpace

open ThresholdFunctions
/-- A quadratic with two ordered real roots is positive outside their closed interval.
[OD14, Example 11.50; elementary sign calculation]

**Proof sketch.** Both linear factors have the same strict sign outside the interval. -/
private lemma factor_pos_of_not_mem {a b x : ℝ} (hab : a < b)
    (hx : ¬ (a ≤ x ∧ x ≤ b)) : 0 < (x-a)*(x-b) := by
  by_cases hax : a ≤ x
  · have hbx : b < x := lt_of_not_ge (fun h => hx ⟨hax,h⟩)
    exact mul_pos (by linarith) (by linarith)
  · exact mul_pos_of_neg_of_neg (by linarith) (by linarith)

/-- The product of interval quadratics is nonpositive exactly on their disjoint union.
[OD14, Example 11.50; elementary sign calculation]

**Proof sketch.** Outside the union every factor is positive. Inside one interval,
its quadratic is nonpositive and all other quadratics are positive. -/
private lemma interval_product_nonpos_iff {m : ℕ} (a b : Fin m → ℝ)
    (hab : ∀ j, a j < b j)
    (hd : Pairwise (fun i j => Disjoint (Set.Icc (a i) (b i)) (Set.Icc (a j) (b j))))
    (x : ℝ) :
    (∏ j, (x-a j)*(x-b j)) ≤ 0 ↔ ∃ j, a j ≤ x ∧ x ≤ b j := by
  classical
  constructor
  · intro h
    by_contra hn
    have hp : 0 < ∏ j, (x-a j)*(x-b j) := Finset.prod_pos fun j _ =>
      factor_pos_of_not_mem (hab j) (fun hx => hn ⟨j,hx⟩)
    linarith
  · rintro ⟨j,hj⟩
    rw [← Finset.mul_prod_erase Finset.univ (fun i => (x-a i)*(x-b i))
      (Finset.mem_univ j)]
    apply mul_nonpos_of_nonpos_of_nonneg
    · exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hj.1) (sub_nonpos.mpr hj.2)
    · apply le_of_lt
      apply Finset.prod_pos
      intro i hi
      apply factor_pos_of_not_mem (hab i)
      intro hx
      exact Set.disjoint_left.mp (hd (Finset.mem_erase.mp hi).1.symm) hj hx

/-- A coordinate minus a constant has total degree at most one.
[OD14, Example 11.50; elementary polynomial degree bound] -/
private lemma coordinate_linear_totalDegree_le {n : ℕ} (s : Fin n) (t : ℝ) :
    (MvPolynomial.X s - MvPolynomial.C t).totalDegree ≤ 1 := by
  simpa using MvPolynomial.totalDegree_sub (MvPolynomial.X s) (MvPolynomial.C t)

/-- A product of `m` coordinate interval quadratics has total degree at most `2*m`.
[OD14, Example 11.50; elementary polynomial degree bound]

**Proof sketch.** Apply subadditivity of total degree to the product and bound
each quadratic by the sum of its two linear degrees. -/
private lemma interval_product_totalDegree_le {n m : ℕ} (s : Fin n) (a b : Fin m → ℝ) :
    (∏ j, (MvPolynomial.X s - MvPolynomial.C (a j)) *
      (MvPolynomial.X s - MvPolynomial.C (b j))).totalDegree ≤ 2*m := by
  calc
    _ ≤ ∑ j, ((MvPolynomial.X s - MvPolynomial.C (a j)) *
        (MvPolynomial.X s - MvPolynomial.C (b j))).totalDegree :=
      MvPolynomial.totalDegree_finset_prod _ _
    _ ≤ ∑ _j : Fin m, 2 := by
      apply Finset.sum_le_sum
      intro j _
      exact (MvPolynomial.totalDegree_mul _ _).trans
        (add_le_add (coordinate_linear_totalDegree_le s _) (coordinate_linear_totalDegree_le s _))
    _ = 2*m := by simp [Nat.mul_comm]

/-- Finitely many disjoint coordinate intervals form a polynomial threshold set of
degree at most twice their number. [OD14, Example 11.50; Kan11]

**Proof sketch.** Negate the product of the endpoint quadratics. Exactly one
quadratic is nonpositive on each interval, and all are positive off their union. -/
lemma interval_threshold_polynomial {n m : ℕ} (s : Fin n) (a b : Fin m → ℝ)
    (hab : ∀ j, a j < b j)
    (hd : Pairwise (fun i j => Disjoint (Set.Icc (a i) (b i)) (Set.Icc (a j) (b j)))) :
    ∃ p : MvPolynomial (Fin n) ℝ, p.totalDegree ≤ 2*m ∧
      {x | 0 ≤ MvPolynomial.eval x p} =
      {x : Fin n → ℝ | ∃ j, a j ≤ x s ∧ x s ≤ b j} := by
  classical
  let f : Fin m → MvPolynomial (Fin n) ℝ :=
    fun j => (MvPolynomial.X s - MvPolynomial.C (a j)) *
      (MvPolynomial.X s - MvPolynomial.C (b j))
  refine ⟨-(∏ j, f j), ?_, ?_⟩
  · rw [MvPolynomial.totalDegree_neg]
    exact interval_product_totalDegree_le s a b
  · ext x
    simp only [Set.mem_setOf_eq, map_neg, neg_nonneg]
    simpa [f, MvPolynomial.eval_prod] using interval_product_nonpos_iff a b hab hd (x s)

/-- One additional root to the right adds a right ray to the nonnegative set.
[OD14, Example 11.50; elementary sign calculation]

**Proof sketch.** Left of the extra root its linear factor reverses the sign of
the interval product; right of that root every factor is nonnegative. -/
private lemma interval_product_extra_root_nonneg_iff {m : ℕ} (a b : Fin m → ℝ)
    (hab : ∀ j, a j < b j)
    (hd : Pairwise (fun i j => Disjoint (Set.Icc (a i) (b i)) (Set.Icc (a j) (b j))))
    (c : ℝ) (hc : ∀ j, b j < c) (x : ℝ) :
    0 ≤ (x-c)*(∏ j, (x-a j)*(x-b j)) ↔
      (∃ j, a j ≤ x ∧ x ≤ b j) ∨ c ≤ x := by
  classical
  by_cases hx : ∃ j, a j ≤ x ∧ x ≤ b j
  · have hxc : x ≤ c := by obtain ⟨j,hj⟩ := hx; exact hj.2.trans (hc j).le
    have hp := (interval_product_nonpos_iff a b hab hd x).mpr hx
    exact iff_of_true (mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hxc) hp)
      (Or.inl hx)
  · have hp : 0 < ∏ j, (x-a j)*(x-b j) :=
      Finset.prod_pos fun j _ => factor_pos_of_not_mem (hab j) (fun h => hx ⟨j,h⟩)
    rw [or_iff_right hx]
    exact (mul_nonneg_iff_of_pos_right hp).trans sub_nonneg

/-- Adding a right ray to disjoint coordinate intervals gives a polynomial threshold
set of degree at most twice the interval count plus one.
[OD14, Example 11.50; Kan11]

**Proof sketch.** Multiply the interval-quadratic product by one more linear
factor, whose root lies beyond every interval. -/
lemma interval_threshold_polynomial_extra_root {n m : ℕ} (s : Fin n) (a b : Fin m → ℝ)
    (hab : ∀ j, a j < b j)
    (hd : Pairwise (fun i j => Disjoint (Set.Icc (a i) (b i)) (Set.Icc (a j) (b j))))
    (c : ℝ) (hc : ∀ j, b j < c) :
    ∃ p : MvPolynomial (Fin n) ℝ, p.totalDegree ≤ 2*m+1 ∧
      {x | 0 ≤ MvPolynomial.eval x p} =
      {x : Fin n → ℝ | (∃ j, a j ≤ x s ∧ x s ≤ b j) ∨ c ≤ x s} := by
  classical
  let f : Fin m → MvPolynomial (Fin n) ℝ :=
    fun j => (MvPolynomial.X s - MvPolynomial.C (a j)) *
      (MvPolynomial.X s - MvPolynomial.C (b j))
  refine ⟨(MvPolynomial.X s - MvPolynomial.C c) * (∏ j, f j), ?_, ?_⟩
  · exact (MvPolynomial.totalDegree_mul _ _).trans
      ((add_le_add (coordinate_linear_totalDegree_le s c)
        (interval_product_totalDegree_le s a b)).trans_eq (Nat.add_comm _ _))
  · ext x
    simpa [f, MvPolynomial.eval_prod] using
      interval_product_extra_root_nonneg_iff a b hab hd c hc (x s)


/-- The standard Gaussian density at zero equals the reciprocal of `sqrt (2*pi)`.
[OD14, Chapter 11; Gaussian density formula] -/
private lemma standardGaussianPDF_zero_eq_inv_sqrt :
    standardGaussianPDF 0 = 1 / Real.sqrt (2 * Real.pi) := by
  simp [standardGaussianPDF_eq]

/-- Disjoint interval endpoints and one extra point can jointly approach the maximum
Gaussian density sum. [OD14, Example 11.50; Kan11]

**Proof sketch.** Scale a fixed ordered grid towards zero. Continuity of the
finite density sums gives both desired estimates at one positive scale. -/
private lemma exists_interval_endpoint_grid (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ (a b : Fin m → ℝ) (c : ℝ),
      (∀ j, a j < b j) ∧
      Pairwise (fun i j => Disjoint (Set.Icc (a i) (b i)) (Set.Icc (a j) (b j))) ∧
      (∀ j, b j < c) ∧
      (2 * (m : ℝ)) * standardGaussianPDF 0 - ε ≤
        ∑ j, (standardGaussianPDF (a j) + standardGaussianPDF (b j)) ∧
      (2 * (m : ℝ) + 1) * standardGaussianPDF 0 - ε ≤
        (∑ j, (standardGaussianPDF (a j) + standardGaussianPDF (b j))) +
          standardGaussianPDF c := by
  let F : ℝ → ℝ := fun t => ∑ j : Fin m,
    (standardGaussianPDF ((2 * (j : ℝ)) * t) +
      standardGaussianPDF ((2 * (j : ℝ) + 1) * t))
  have hF : Continuous F := by
    apply continuous_finset_sum
    intro j hj
    exact (continuous_standardGaussianPDF.comp (continuous_const.mul continuous_id)).add
      (continuous_standardGaussianPDF.comp (continuous_const.mul continuous_id))
  have hF0 : F 0 = (2 * (m : ℝ)) * standardGaussianPDF 0 := by
    simp [F]
    ring
  have hG : Continuous (fun t => F t + standardGaussianPDF ((2 * (m : ℝ) + 1) * t)) :=
    hF.add (continuous_standardGaussianPDF.comp (continuous_const.mul continuous_id))
  have he : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      (2 * (m : ℝ)) * standardGaussianPDF 0 - ε < F t := by
    apply (hF.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).eventually
    rw [hF0]
    exact Ioi_mem_nhds (by linarith)
  have ho : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      (2 * (m : ℝ) + 1) * standardGaussianPDF 0 - ε <
        F t + standardGaussianPDF ((2 * (m : ℝ) + 1) * t) := by
    apply (hG.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).eventually
    simp only [mul_zero, hF0]
    exact Ioi_mem_nhds (by linarith)
  have hc : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧
      (2 * (m : ℝ)) * standardGaussianPDF 0 - ε < F t ∧
      (2 * (m : ℝ) + 1) * standardGaussianPDF 0 - ε <
        F t + standardGaussianPDF ((2 * (m : ℝ) + 1) * t) := by
    filter_upwards [self_mem_nhdsWithin, he, ho] with t ht he ho
    exact ⟨ht, he, ho⟩
  obtain ⟨t, ht, he, ho⟩ := hc.exists
  refine ⟨fun j => (2 * (j : ℝ)) * t, fun j => (2 * (j : ℝ) + 1) * t,
    (2 * (m : ℝ) + 1) * t, ?_, ?_, ?_, he.le, ho.le⟩
  · intro j
    nlinarith
  · intro i j hij
    rw [Set.disjoint_left]
    intro x hx hy
    rcases lt_or_gt_of_ne hij with h | h
    · have hv : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast h
      nlinarith [hx.2, hy.1]
    · have hv : (j : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast h
      nlinarith [hx.1, hy.2]
  · intro j
    have hj : (j : ℝ) < (m : ℝ) := by exact_mod_cast j.isLt
    nlinarith



/-- Adding a closed interval strictly to the right preserves pairwise disjointness.
[OD14, Example 11.50; elementary interval separation]

**Proof sketch.** The new interval is separated from every old interval by its
left endpoint; Mathlib's finite-successor pairwise criterion handles the indices. -/
private lemma pairwise_disjoint_intervals_cons {m : ℕ} (a b : Fin m → ℝ)
    (hd : Pairwise (fun i j => Disjoint (Set.Icc (a i) (b i)) (Set.Icc (a j) (b j))))
    (c M : ℝ) (hc : ∀ j, b j < c) :
    Pairwise (fun i j => Disjoint
      (Set.Icc ((Fin.cons c a : Fin (m + 1) → ℝ) i)
        ((Fin.cons M b : Fin (m + 1) → ℝ) i))
      (Set.Icc ((Fin.cons c a : Fin (m + 1) → ℝ) j)
        ((Fin.cons M b : Fin (m + 1) → ℝ) j))) := by
  rw [pairwise_fin_succ_iff]
  simp only [Fin.cons_zero, Fin.cons_succ]
  refine ⟨?_, ?_, hd⟩
  · intro j
    rw [Set.disjoint_left]
    intro x hx hy
    exact (hc j).not_ge (hy.1.trans hx.2)
  · intro j
    rw [Set.disjoint_left]
    intro x hx hy
    exact (hc j).not_ge (hx.1.trans hy.2)

/-- A finite coordinate interval union together with a coordinate ray is measurable.
[OD14, Example 11.50; elementary Borel measurability] -/
private lemma measurableSet_coordinate_intervals_union_ray {n m : ℕ} (s : Fin n)
    (a b : Fin m → ℝ) (c : ℝ) :
    MeasurableSet {x : Fin n → ℝ | (∃ j, a j ≤ x s ∧ x s ≤ b j) ∨ c ≤ x s} := by
  change MeasurableSet ({x : Fin n → ℝ | ∃ j, a j ≤ x s ∧ x s ≤ b j} ∪
    {x : Fin n → ℝ | c ≤ x s})
  apply MeasurableSet.union
  · simp only [show {x : Fin n → ℝ | ∃ j, a j ≤ x s ∧ x s ≤ b j} =
      ⋃ j, {x : Fin n → ℝ | a j ≤ x s ∧ x s ≤ b j} by ext; simp]
    exact MeasurableSet.iUnion fun j =>
      (measurableSet_le measurable_const (measurable_pi_apply s)).inter
        (measurableSet_le (measurable_pi_apply s) measurable_const)
  · exact measurableSet_le measurable_const (measurable_pi_apply s)

/-- Cutting off a coordinate interval union and right ray yields one extra interval.
[OD14, Example 11.50; elementary interval identity]

**Proof sketch.** Old intervals lie below the cutoff. The ray is truncated to
the closed interval between its endpoint and the cutoff. -/
private lemma coordinate_intervals_union_ray_inter {n m : ℕ} (s : Fin n)
    (a b : Fin m → ℝ) (c M : ℝ) (hM : ∀ j, b j ≤ M) :
    {x : Fin n → ℝ | (∃ j, a j ≤ x s ∧ x s ≤ b j) ∨ c ≤ x s} ∩
      {x | x s ≤ M} =
    {x : Fin n → ℝ | ∃ j : Fin (m + 1),
      (Fin.cons c a : Fin (m + 1) → ℝ) j ≤ x s ∧
        x s ≤ (Fin.cons M b : Fin (m + 1) → ℝ) j} := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Fin.exists_fin_succ,
    Fin.cons_zero, Fin.cons_succ]
  constructor
  · rintro ⟨hx, hxM⟩
    rcases hx with ⟨j, hj⟩ | hx
    · exact Or.inr ⟨j, hj⟩
    · exact Or.inl ⟨hx, hxM⟩
  · rintro (hx | ⟨j, hj⟩)
    · exact ⟨Or.inr hx.1, hx.2⟩
    · exact ⟨Or.inl ⟨j, hj⟩, hj.2.trans (hM j)⟩

/-- A disjoint union of coordinate intervals and a separated right ray has surface
area at least the sum of its finite-endpoint Gaussian densities.
[OD14, Example 11.50; Ex. 11.16]

**Proof sketch.** Intersect with a halfspace beyond the ray endpoint. The interval
formula computes the resulting perimeter. Intersection subadditivity and the
halfspace formula let us cancel the artificial endpoint contribution. -/
lemma interval_ray_surfaceArea_lower_bound {n : ℕ} (s : Fin n)
    {m : ℕ} (a b : Fin m → ℝ) (hab : ∀ j, a j < b j)
    (hd : Pairwise (fun i j => Disjoint (Set.Icc (a i) (b i)) (Set.Icc (a j) (b j))))
    (c : ℝ) (hc : ∀ j, b j < c) :
    ENNReal.ofReal ((∑ j, (standardGaussianPDF (a j) + standardGaussianPDF (b j))) +
      standardGaussianPDF c) ≤
    gaussianSurfaceArea {x : Fin n → ℝ | (∃ j, a j ≤ x s ∧ x s ≤ b j) ∨ c ≤ x s} := by
  classical
  let A := {x : Fin n → ℝ | (∃ j, a j ≤ x s ∧ x s ≤ b j) ∨ c ≤ x s}
  let B := {x : Fin n → ℝ | x s ≤ c+1}
  have hcut := surfaceArea_coordinate_disjoint_intervals s
    (Fin.cons c a) (Fin.cons (c+1) b)
    (by
      simp only [Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ]
      exact ⟨by linarith, hab⟩)
    (pairwise_disjoint_intervals_cons a b hd c (c+1) hc)
  have hhalf : gaussianSurfaceArea B = ENNReal.ofReal (standardGaussianPDF (c+1)) := by
    simpa [B, Pi.single_apply] using surfaceArea_halfspace (Pi.single s (1 : ℝ))
      (by simp [Pi.single_apply]) (c+1)
  have h := surfaceArea_inter_le (measurableSet_coordinate_intervals_union_ray s a b c)
    (measurableSet_le (measurable_pi_apply s) (measurable_const (a := c+1)))
  rw [coordinate_intervals_union_ray_inter s a b c (c+1) (fun j => (hc j).le.trans
    (by linarith)), hcut, hhalf] at h
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] at h
  rw [show standardGaussianPDF c + standardGaussianPDF (c+1) +
      ∑ j, (standardGaussianPDF (a j) + standardGaussianPDF (b j)) =
      (∑ j, (standardGaussianPDF (a j) + standardGaussianPDF (b j))) +
      standardGaussianPDF c + standardGaussianPDF (c+1) by ring,
    ENNReal.ofReal_add
      (add_nonneg (Finset.sum_nonneg fun j _ => add_nonneg
        (standardGaussianPDF_pos _).le (standardGaussianPDF_pos _).le)
        (standardGaussianPDF_pos c).le) (standardGaussianPDF_pos (c+1)).le] at h
  exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).mp h

/-- The polynomial threshold surface-area degree bound can be approached in any
nonempty ambient dimension using only one coordinate.
[OD14, Example 11.50; Kan11]

**Proof sketch.** Place the required number of roots near zero using a scaled
grid. For even degree use disjoint intervals; for odd degree add a right ray.
The endpoint density sum approaches the degree times the Gaussian density at zero. -/
lemma exists_coordinate_polynomial_threshold_surfaceArea_ge
    {n : ℕ} (s : Fin n)
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ p : MvPolynomial (Fin n) ℝ, p.totalDegree ≤ k ∧
      ENNReal.ofReal ((k : ℝ) / Real.sqrt (2 * Real.pi) - ε) ≤
        gaussianSurfaceArea {x : Fin n → ℝ | 0 ≤ MvPolynomial.eval x p} := (by
  let m := k / 2
  obtain ⟨a,b,c,hab,hd,hc,heven,hodd⟩ := exists_interval_endpoint_grid m ε hε
  have hk : k = 2*m ∨ k = 2*m+1 := by dsimp [m]; omega
  rcases hk with hk | hk
  · obtain ⟨p,hp,heq⟩ := interval_threshold_polynomial s a b hab hd
    refine ⟨p, hk ▸ hp, ?_⟩
    rw [heq, surfaceArea_coordinate_disjoint_intervals s a b hab hd]
    apply ENNReal.ofReal_le_ofReal
    simpa [hk, standardGaussianPDF_zero_eq_inv_sqrt, div_eq_mul_inv] using heven
  · obtain ⟨p,hp,heq⟩ := interval_threshold_polynomial_extra_root s a b hab hd c hc
    refine ⟨p, hk ▸ hp, ?_⟩
    rw [heq]
    exact (ENNReal.ofReal_le_ofReal (by
      simpa [hk, standardGaussianPDF_zero_eq_inv_sqrt, div_eq_mul_inv] using hodd)).trans
      (interval_ray_surfaceArea_lower_bound s a b hab hd c hc)
)

end BooleanAnalysis.GaussianSpace


