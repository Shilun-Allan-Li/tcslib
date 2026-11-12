/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Hermite.Basis
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.MeasureTheory.Function.LpSpace.Complete

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Finite-degree Gaussian Hermite approximations

## Main definitions

* `hermiteDegreeIndices`: the finite set of multi-indices below a total-degree cutoff.

## Main results

Finite-degree Hermite sums converge in Gaussian L².

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.2, Definition 11.34 and Proposition 11.36.
-/

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace BooleanAnalysis.GaussianSpace

open ThresholdFunctions

variable {n : ℕ}
local notation "γ" => (Measure.pi fun _ : Fin n => standardGaussianMeasure)

open scoped Classical in
/-- The finite set of multi-indices of total degree at most `k`.
[OD14, Def. 11.34, displayed expansion] -/
noncomputable def hermiteDegreeIndices (k : ℕ) : Finset (Fin n → ℕ) :=
  ((Finset.univ : Finset (Fin n → Fin (k + 1))).image
    (fun a i => (a i : ℕ))).filter (fun α => (∑ i, α i) ≤ k)

/-- A multi-index belongs to a degree cutoff exactly when its total degree is
at most the cutoff.

**Proof sketch.** Each coordinate is at most the total degree, so every index
of sufficiently small total degree occurs in the bounded-coordinate enumeration. -/
@[simp] lemma mem_hermiteDegreeIndices (k : ℕ) (α : Fin n → ℕ) :
    α ∈ hermiteDegreeIndices (n := n) k ↔ (∑ i, α i) ≤ k := by
  classical
  simp only [hermiteDegreeIndices, Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro hα
    refine ⟨Finset.mem_image.mpr
      ⟨(fun i => ⟨α i, ?_⟩), Finset.mem_univ _, rfl⟩, hα⟩
    exact Nat.lt_succ_of_le
      ((Finset.single_le_sum (fun j _ => Nat.zero_le (α j)) (Finset.mem_univ i)).trans hα)

/-- Increasing total-degree cutoffs eventually contain every finite set of
multi-indices.

**Proof sketch.** The cutoffs are increasing, and each index belongs to the
cutoff at its own total degree. -/
lemma hermiteDegreeIndices_tendsto :
    Tendsto (hermiteDegreeIndices (n := n)) atTop atTop := by
  apply Monotone.tendsto_atTop_finset
  · intro k l hkl α hα
    exact (mem_hermiteDegreeIndices l α).2
      (((mem_hermiteDegreeIndices k α).1 hα).trans hkl)
  · intro α
    exact ⟨∑ i, α i, (mem_hermiteDegreeIndices _ α).2 le_rfl⟩

/-- Summing over a degree cutoff equals the bounded-coordinate sum that discards
indices whose total degree exceeds the cutoff.

**Proof sketch.** Rewrite the filter as a conditional sum and remove the image
using injectivity of the coordinatewise natural-number cast. -/
lemma sum_hermiteDegreeIndices {E : Type*} [AddCommMonoid E]
    (k : ℕ) (v : (Fin n → ℕ) → E) :
    (∑ α ∈ hermiteDegreeIndices (n := n) k, v α) =
      ∑ a : Fin n → Fin (k + 1),
        if (∑ i, (a i : ℕ)) ≤ k then v (fun i => (a i : ℕ)) else 0 := by
  classical
  unfold hermiteDegreeIndices
  rw [Finset.sum_filter, Finset.sum_image]
  intro a ha b hb hab
  funext i
  exact Fin.ext (congrFun hab i)

/-- A finite linear combination of Hermite L² classes is represented almost
everywhere by the corresponding concrete Hermite sum. [OD14, Def. 11.34]

**Proof sketch.** Finite addition and scalar multiplication preserve
almost-everywhere representatives. Each Hermite class is represented by its
concrete polynomial function. -/
lemma coeFn_sum_hermiteL2 (s : Finset (Fin n → ℕ)) (c : (Fin n → ℕ) → ℝ) :
    (fun x => (∑ α ∈ s, c α • hermiteL2 α : Lp ℝ 2 γ) x) =ᵐ[γ]
      (fun x => ∑ α ∈ s, c α * hermiteFunction α x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa only [Finset.sum_empty] using (Lp.coeFn_zero ℝ 2 γ)
  | @insert α s hα ih =>
      simp only [Finset.sum_insert hα]
      filter_upwards
        [Lp.coeFn_add (c α • hermiteL2 α) (∑ β ∈ s, c β • hermiteL2 β),
          Lp.coeFn_smul (c α) (hermiteL2 α),
          (hermiteFunction_memLp_two α).coeFn_toLp, ih] with x hadd hsmul hHermite hsum
      change hermiteL2 α x = hermiteFunction α x at hHermite
      simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        hsmul, hHermite, hsum] using hadd

/-- Hermite sums truncated by total degree converge to the function in L².
[OD14, Def. 11.34, displayed expansion]
**Proof sketch.** Restrict the complete orthonormal expansion to the increasing
finite sets of multi-indices of total degree at most the cutoff. -/
theorem hermite_degree_truncation_tendsto (f : (Fin n → ℝ) → ℝ) (hf : MemLp f 2 γ) :
    Tendsto (fun k : ℕ => eLpNorm (fun x => f x -
      ∑ a : Fin n → Fin (k + 1), if (∑ i, (a i : ℕ)) ≤ k then
        hermiteCoeff f (fun i => (a i : ℕ)) * hermiteFunction (fun i => (a i : ℕ)) x else 0)
      2 γ) atTop (𝓝 0) := by
  classical
  have hsum : Tendsto
      (fun s : Finset (Fin n → ℕ) => ∑ α ∈ s, hermiteCoeff f α • hermiteL2 α)
      atTop (𝓝 (hf.toLp f)) :=
    hermite_expansion f hf
  have hnorm := (Lp.tendsto_Lp_iff_tendsto_eLpNorm
    (fun k : ℕ => ∑ α ∈ hermiteDegreeIndices (n := n) k,
      hermiteCoeff f α • hermiteL2 α) f hf).1
    (hsum.comp (hermiteDegreeIndices_tendsto (n := n)))
  refine hnorm.congr' (Filter.Eventually.of_forall fun k => ?_)
  rw [eLpNorm_sub_comm]
  apply eLpNorm_congr_ae
  filter_upwards [coeFn_sum_hermiteL2 (hermiteDegreeIndices (n := n) k)
    (hermiteCoeff f)] with x hx
  simp only [Pi.sub_apply]
  rw [hx, sum_hermiteDegreeIndices]

end BooleanAnalysis.GaussianSpace
