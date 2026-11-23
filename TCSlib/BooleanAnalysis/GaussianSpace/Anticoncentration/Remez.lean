/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.Interpolation
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Fin.Basic
import Mathlib.Analysis.Complex.Exponential

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Univariate polynomial Remez estimates

This file selects interpolation nodes from sets of positive Lebesgue measure
and proves a univariate Remez estimate with a degree-independent base constant.

## Main definitions

The existing Lebesgue outer measure and finite sets are reused.

## Main results

* `exists_separated_finset_of_measure_gt`: sufficiently large outer measure
  supplies a prescribed number of separated real points.
* `exists_index_separated_nodes_of_measure_gt`: increasing nodes have distances
  bounded below by their index separation.
* `abs_eval_le_of_bound_on_set`: a bound on a positive-measure subset extends
  to its containing interval with Remez factor `(4 exp(2) length / measure)^d`.

## References

* [CW01] A. Carbery and J. Wright, Distributional and Lq norm inequalities for
  polynomials over convex bodies in Rn, Mathematical Research Letters 8 (2001),
  233–248, §4, the univariate Remez stage.
-/

open MeasureTheory
open scoped BigOperators

namespace BooleanAnalysis.GaussianSpace.PolynomialAnticoncentration

/-- If `E` has real Lebesgue measure greater than `2dδ`, it contains `d+1`
points whose pairwise distances exceed `δ`.

**Proof sketch.** Select points inductively. Each previously selected point
excludes a closed interval of length `2δ`. The union of at most `d` such
intervals has measure at most `2dδ`, so it cannot contain `E`. Choose the next
point outside that union. Outer-measure monotonicity suffices, so `E` need
not be measurable. -/
lemma exists_separated_finset_of_measure_gt (E : Set ℝ) (d : ℕ)
    {δ : ℝ} (hδ : 0 < δ)
    (hmeasure : 2 * (d : ℝ) * δ < volume.real E) :
    ∃ s : Finset ℝ, s.card = d + 1 ∧
      (↑s : Set ℝ) ⊆ E ∧
      ∀ x ∈ s, ∀ y ∈ s, x ≠ y → δ < |x - y| := (by
  classical
  induction d with
  | zero =>
    have hpos : 0 < volume.real E := by simpa using hmeasure
    obtain ⟨x, hx⟩ := nonempty_of_measureReal_ne_zero hpos.ne'
    refine ⟨{x}, by simp, ?_, ?_⟩
    · simpa using hx
    · simp
  | succ d ih =>
    obtain ⟨s, hcard, hsE, hsep⟩ := ih (by
      have : (0 : ℝ) < 2 * δ := by positivity
      push_cast at hmeasure
      linarith)
    let U : Set ℝ := ⋃ y ∈ s, Set.Icc (y - δ) (y + δ)
    have hUfin : volume U ≠ ⊤ :=
      measure_biUnion_ne_top s.finite_toSet (fun _ _ => measure_Icc_lt_top.ne)
    have hUmeasure : volume.real U ≤ 2 * ((d + 1 : ℕ) : ℝ) * δ := by
      have hint (y : ℝ) :
          volume.real (Set.Icc (y - δ) (y + δ)) = 2 * δ := by
        rw [Real.volume_real_Icc_of_le (by linarith)]
        ring
      calc
        _ ≤ ∑ y ∈ s, volume.real (Set.Icc (y - δ) (y + δ)) :=
          measureReal_biUnion_finset_le s _
        _ = _ := by
          simp only [hint, Finset.sum_const, hcard, nsmul_eq_mul]
          ring
    have hnot : ¬ E ⊆ U := by
      intro h
      have hm := measureReal_mono h hUfin
      exact (not_lt_of_ge (hm.trans hUmeasure)) hmeasure
    obtain ⟨x, hx, hxU⟩ := Set.not_subset.mp hnot
    have hdist : ∀ y ∈ s, δ < |x - y| := by
      intro y hy
      by_contra h
      have hab := abs_le.mp (le_of_not_gt h)
      apply hxU
      exact Set.mem_iUnion.mpr ⟨y, Set.mem_iUnion.mpr ⟨hy, by
        constructor <;> linarith [hab.1, hab.2]⟩⟩
    have hxnot : x ∉ s := by
      intro h
      have hbad : δ < 0 := by simpa using hdist x h
      exact (not_lt_of_ge hδ.le) hbad
    refine ⟨insert x s, by simp [hxnot, hcard], ?_, ?_⟩
    · intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hx
      · exact hsE hy
    · intro y hy z hz hyz
      by_cases hyx : y = x
      · subst y
        rcases Finset.mem_insert.mp hz with hzx | hzs
        · exact (hyz hzx.symm).elim
        · exact hdist z hzs
      · have hys : y ∈ s := (Finset.mem_insert.mp hy).resolve_left hyx
        by_cases hzx : z = x
        · subst z
          rw [abs_sub_comm]
          exact hdist y hys
        · exact hsep y hys z ((Finset.mem_insert.mp hz).resolve_left hzx) hyz
)


/-- Adjacent increments bounded below by `δ` give the corresponding
absolute-distance bound between arbitrary indices.

**Proof sketch.** Subtract `δ` times the index from each value. The adjacent
gap hypothesis makes this modified sequence monotone. Compare two ordered
indices and use that an absolute difference dominates either signed difference. -/
lemma mul_abs_sub_le_abs_sub_of_adjacent_gaps (n : ℕ)
    (v : Fin (n + 1) → ℝ) (δ : ℝ)
    (hadj : ∀ i : Fin n, δ ≤ v i.succ - v i.castSucc)
    (i j : Fin (n + 1)) :
    δ * |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| ≤ |v i - v j| := (by
  have hmono : Monotone (fun k : Fin (n + 1) => v k - δ * ((k : ℕ) : ℝ)) := by
    apply Fin.monotone_iff_le_succ.mpr
    intro k
    have h := hadj k
    change v k.castSucc - δ * ((k : ℕ) : ℝ) ≤
      v k.succ - δ * (((k : ℕ) + 1 : ℕ) : ℝ)
    push_cast
    linarith
  rcases le_total i j with hij | hji
  · have h := hmono hij
    rw [abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast hij))]
    calc
      _ ≤ v j - v i := by linarith
      _ ≤ |v i - v j| := by simpa only [neg_sub] using neg_le_abs (v i - v j)
  · have h := hmono hji
    rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hji))]
    calc
      _ ≤ v i - v j := by linarith
      _ ≤ |v i - v j| := le_abs_self _
)


/-- A sufficiently large real Lebesgue measure supplies indexed nodes whose
distances dominate `δ` times their index distances.

**Proof sketch.** Select a separated finite subset and enumerate it increasingly.
Its adjacent increments exceed `δ`, so the adjacent-gap lemma bounds all index
differences. Extend this enumeration arbitrarily beyond index `d`. -/
lemma exists_index_separated_nodes_of_measure_gt (E : Set ℝ) (d : ℕ)
    {δ : ℝ} (hδ : 0 < δ)
    (hmeasure : 2 * (d : ℝ) * δ < volume.real E) :
    ∃ v : ℕ → ℝ,
      (∀ i ≤ d, v i ∈ E) ∧
      ∀ i ≤ d, ∀ j ≤ d,
        δ * |(i : ℝ) - (j : ℝ)| ≤ |v i - v j| := (by
    classical
    obtain ⟨s, hcard, hsE, hsep⟩ :=
      exists_separated_finset_of_measure_gt E d hδ hmeasure
    let w : Fin (d + 1) ↪o ℝ := s.orderEmbOfFin hcard
    have hwmem (i : Fin (d + 1)) : w i ∈ s :=
      s.orderEmbOfFin_mem hcard i
    have hadj (i : Fin d) : δ ≤ w i.succ - w i.castSucc := by
      have hlt : w i.castSucc < w i.succ := w.strictMono (Fin.castSucc_lt_succ i)
      have h := hsep (w i.succ) (hwmem i.succ)
        (w i.castSucc) (hwmem i.castSucc) (ne_of_gt hlt)
      rw [abs_of_pos (sub_pos.mpr hlt)] at h
      exact h.le
    let v : ℕ → ℝ := fun i => if hi : i < d + 1 then w ⟨i, hi⟩ else 0
    have hv (i : ℕ) (hi : i ≤ d) : v i = w ⟨i, by omega⟩ := by
      simp only [v, dif_pos (by omega : i < d + 1)]
    refine ⟨v, ?_, ?_⟩
    · intro i hi
      rw [hv i hi]
      exact hsE (hwmem _)
    · intro i hi j hj
      rw [hv i hi, hv j hj]
      exact mul_abs_sub_le_abs_sub_of_adjacent_gaps d w δ hadj
        ⟨i, by omega⟩ ⟨j, by omega⟩
)


/-- The ratio `(d+1)^d / d!` is at most `(exp 2)^d`.

**Proof sketch.** For positive `d`, the exponential-series estimate bounds
the ratio by `exp (d+1)`, which is at most `exp (2d)`. The case `d = 0`
is an equality. -/
lemma succ_pow_div_factorial_le_exp_two_pow (d : ℕ) :
    (((d + 1 : ℕ) : ℝ) ^ d) / (d.factorial : ℝ) ≤
      (Real.exp 2) ^ d := (by
  rcases d with _ | d
  · simp
  · calc
      _ ≤ Real.exp ((d + 1 + 1 : ℕ) : ℝ) :=
        Real.pow_div_factorial_le_exp _ (by positivity) (d + 1)
      _ ≤ Real.exp (((d + 1 : ℕ) : ℝ) * 2) := by
        apply Real.exp_le_exp.mpr
        push_cast
        linarith
      _ = _ := Real.exp_nat_mul 2 (d + 1)
)


/-- A polynomial bounded on a subset of positive real Lebesgue measure is
bounded throughout the containing interval by a universal-base Remez estimate.
Cf. [CW01, §4]. The constant `4 exp 2` is deliberately coarser than the
best-constant formulation, as it suffices for subsequent distribution bounds.

**Proof sketch.** Set `δ = volume.real E / (2(d+1))` and select indexed
`δ`-separated nodes in `E`. Every node lies within `b-a` of `x`.
Apply the quantitative interpolation bound, then absorb `(d+1)^d / d!`
into `(exp 2)^d`. -/
lemma abs_eval_le_of_bound_on_set (p : Polynomial ℝ) (d : ℕ)
    (hp : p.natDegree ≤ d) (E : Set ℝ) (a b M : ℝ)
    (hab : a ≤ b) (hE : E ⊆ Set.Icc a b)
    (hmeasure : 0 < volume.real E) (hM : 0 ≤ M)
    (hvalue : ∀ y ∈ E, |p.eval y| ≤ M)
    (x : ℝ) (hx : x ∈ Set.Icc a b) :
    |p.eval x| ≤
      M * (4 * Real.exp 2 * (b - a) / volume.real E) ^ d := (by
  let δ : ℝ := volume.real E / (2 * ((d + 1 : ℕ) : ℝ))
  have hdpos : (0 : ℝ) < ((d + 1 : ℕ) : ℝ) := by positivity
  have hδ : 0 < δ := div_pos hmeasure (by positivity)
  have hsmall : 2 * (d : ℝ) * δ < volume.real E := by
    dsimp only [δ]
    rw [← mul_div_assoc, div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * ((d + 1 : ℕ) : ℝ))]
    push_cast
    nlinarith
  obtain ⟨v, hvE, hsep⟩ :=
    exists_index_separated_nodes_of_measure_gt E d hδ hsmall
  have hdist (i : ℕ) (hi : i ≤ d) : |x - v i| ≤ b - a := by
    have hvi := hE (hvE i hi)
    apply abs_le.mpr
    constructor <;> linarith [hx.1, hx.2, hvi.1, hvi.2]
  have hinterp := abs_eval_le_of_separated_nodes p d hp v hδ (sub_nonneg.mpr hab)
    hM hsep x hdist (fun i hi => hvalue (v i) (hvE i hi))
  have hbase : 2 * (b - a) / δ =
      (4 * (b - a) / volume.real E) * ((d + 1 : ℕ) : ℝ) := by
    dsimp only [δ]
    field_simp
    ring
  calc
    |p.eval x| ≤ M / (d.factorial : ℝ) * (2 * (b - a) / δ) ^ d := hinterp
    _ = (M * (4 * (b - a) / volume.real E) ^ d) *
        ((((d + 1 : ℕ) : ℝ) ^ d) / (d.factorial : ℝ)) := by
      rw [hbase, mul_pow]
      ring
    _ ≤ (M * (4 * (b - a) / volume.real E) ^ d) * (Real.exp 2) ^ d :=
      mul_le_mul_of_nonneg_left (succ_pow_div_factorial_le_exp_two_pow d)
        (mul_nonneg hM (pow_nonneg (div_nonneg (by linarith) hmeasure.le) _))
    _ = M * (4 * Real.exp 2 * (b - a) / volume.real E) ^ d := by
      rw [mul_assoc, ← mul_pow]
      congr 2
      ring
)

end BooleanAnalysis.GaussianSpace.PolynomialAnticoncentration
