/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty, Mina Sha
-/

import TCSlib.BooleanAnalysis.Hypercontractivity.Cube.Basic
import TCSlib.BooleanAnalysis.Hypercontractivity.Applications.KKL.Basic
import Mathlib.Data.Finset.Piecewise

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Coordinate averaging and Boolean junta rounding

## Main definitions

No new definitions. Coordinate restrictions use `Finset.piecewise`.

## Main results

* `expect_coordinateRestriction_eq_sum_fourier`: coordinate averaging is Fourier projection.
* `expect_disagreement_coordinateRestriction`: Boolean restriction rounding has half
  the omitted Fourier weight in expected disagreement.
* `exists_boolean_constant_approximation`: a Boolean constant achieves half the variance.
* `exists_boolean_junta_of_fourier_omission`: a Boolean junta achieves half the
  omitted Fourier weight as an upper bound on disagreement.
* `expect_chiS_coordinateRestriction`: averaging a parity character outside `J`
  preserves it when its Fourier set lies in `J`, and otherwise gives zero.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014, §3.3, Proposition 3.21 and Exercise 3.34.
-/

open scoped BigOperators Classical

namespace BooleanAnalysis.Hypercontractivity

/-- Fixing coordinates in `J` and uniformly averaging the remaining coordinates
preserves the character on `S` when `S ⊆ J`, and otherwise gives zero.
[OD14, §3.3, Prop. 3.21]
This identity includes empty coordinate sets and the zero-dimensional cube.

**Proof sketch.** If `S` is contained in `J`, every coordinate used by the character
is fixed, so the character is constant under averaging. Otherwise choose a coordinate
in `S` outside `J`. Flipping that coordinate is a bijection on the averaged cube and
negates the character, pairing contributions of opposite sign and forcing mean zero. -/
lemma expect_chiS_coordinateRestriction {n : ℕ} (S J : Finset (Fin n))
    (x : BoolCube n) :
    expect (fun y => chiS S (J.piecewise x y)) =
      if S ⊆ J then chiS S x else 0 :=
  (by
  classical
  by_cases hS : S ⊆ J
  · rw [if_pos hS]
    have hconst (y : BoolCube n) :
        chiS S (J.piecewise x y) = chiS S x := by
      unfold chiS
      apply Finset.prod_congr rfl
      intro j hj
      rw [Finset.piecewise_eq_of_mem J x y (hS hj)]
    simp only [hconst, ThresholdFunctions.expect_const]
  · rw [if_neg hS]
    obtain ⟨i, hiS, hiJ⟩ := Finset.not_subset.mp hS
    have hpiece (y : BoolCube n) :
        J.piecewise x (flipBit y i) = flipBit (J.piecewise x y) i := by
      funext j
      by_cases hji : j = i
      · subst j
        simp [flipBit, Finset.piecewise, hiJ]
      · simp [flipBit, Finset.piecewise, hji]
    have hbij : Function.Bijective (fun y : BoolCube n => flipBit y i) :=
      (show Function.Involutive (fun y : BoolCube n => flipBit y i) from
        fun y => flipBit_flipBit y i).bijective
    have hflip := Fintype.expect_bijective
      (fun y : BoolCube n => flipBit y i) hbij
      (fun y => chiS S (J.piecewise x (flipBit y i)))
      (fun y => chiS S (J.piecewise x y)) (fun _ => rfl)
    simp only [← expect_eq_fintypeExpect, hpiece, chiS_flipBit_eq,
      if_pos hiS, ThresholdFunctions.expect_neg] at hflip
    linarith
)

/-- Averaging a real-valued cube function outside `J` retains exactly the Fourier
terms whose coordinate sets are contained in `J`. [OD14, §3.3, Prop. 3.21]

**Proof sketch.** Expand the function in Walsh characters and exchange the finite
expectation with the Fourier sum. Coordinate averaging preserves characters supported
in `J` and annihilates every other character. -/
lemma expect_coordinateRestriction_eq_sum_fourier {n : ℕ} (f : BooleanFunc n)
    (J : Finset (Fin n)) (x : BoolCube n) :
    expect (fun y => f (J.piecewise x y)) =
      ∑ S : Finset (Fin n), if S ⊆ J then fourierCoeff f S * chiS S x else 0 :=
  (by
  classical
  calc
    expect (fun y => f (J.piecewise x y)) =
        expect (fun y => ∑ S : Finset (Fin n),
          fourierCoeff f S * chiS S (J.piecewise x y)) := by
      exact congrArg expect
        (funext fun y => walsh_expansion f (J.piecewise x y))
    _ = ∑ S : Finset (Fin n),
        expect (fun y => fourierCoeff f S * chiS S (J.piecewise x y)) := by
      simp_rw [expect_eq_fintypeExpect, Finset.expect_sum_comm]
    _ = ∑ S : Finset (Fin n),
        if S ⊆ J then fourierCoeff f S * chiS S x else 0 := by
      apply Finset.sum_congr rfl
      intro S _
      rw [ThresholdFunctions.expect_const_mul, expect_chiS_coordinateRestriction]
      by_cases hS : S ⊆ J <;> simp [hS]
)

/-- The average disagreement between a ±1-valued cube function and a uniformly
random restriction outside `J` is half its Fourier weight on sets not contained in `J`.
[OD14, Ex. 3.34; Thm. 9.28, proof]
This randomized restriction identity includes empty and full coordinate sets and
the zero-dimensional cube.

**Proof sketch.** For Boolean values, the disagreement indicator equals half of
one minus the product of the two values. Exchange the finite averages over the
input and the restriction, then use the coordinate-average Fourier projection.
Fourier orthogonality gives the sum of squared coefficients supported in `J`.
Parseval and the ±1 hypothesis make the total squared Fourier weight equal to one,
so subtracting the retained weight leaves exactly the stated Fourier tail. -/
lemma expect_disagreement_coordinateRestriction {n : ℕ} (f : BooleanFunc n)
    (hf : isPmOne f) (J : Finset (Fin n)) :
    expect (fun z => ThresholdFunctions.disagreementProbability f
      (fun x => f (J.piecewise x z))) =
      (1 / 2) * (∑ S : Finset (Fin n),
        if S ⊆ J then 0 else fourierCoeff f S ^ 2) :=
  (by
  classical
  have hindicator (x z : BoolCube n) :
      (if f x = f (J.piecewise x z) then (0 : ℝ) else 1) =
        (1 / 2) * (1 - f x * f (J.piecewise x z)) := by
    rcases hf x with hx | hx <;>
      rcases hf (J.piecewise x z) with hz | hz <;>
        norm_num [hx, hz]
  have hcorrelation :
      expect (fun x => f x * expect (fun z => f (J.piecewise x z))) =
        ∑ S : Finset (Fin n), if S ⊆ J then fourierCoeff f S ^ 2 else 0 := by
    calc
      expect (fun x => f x * expect (fun z => f (J.piecewise x z))) =
          expect (fun x => ∑ S : Finset (Fin n),
            if S ⊆ J then fourierCoeff f S * (f x * chiS S x) else 0) := by
        apply congrArg expect
        funext x
        rw [expect_coordinateRestriction_eq_sum_fourier, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro S _
        by_cases hS : S ⊆ J
        · simp only [if_pos hS]
          ring
        · simp [hS]
      _ = ∑ S : Finset (Fin n),
          expect (fun x =>
            if S ⊆ J then fourierCoeff f S * (f x * chiS S x) else 0) := by
        simp_rw [expect_eq_fintypeExpect, Finset.expect_sum_comm]
      _ = ∑ S : Finset (Fin n),
          if S ⊆ J then fourierCoeff f S ^ 2 else 0 := by
        apply Finset.sum_congr rfl
        intro S _
        by_cases hS : S ⊆ J
        · simp only [if_pos hS, ThresholdFunctions.expect_const_mul]
          change fourierCoeff f S * fourierCoeff f S = fourierCoeff f S ^ 2
          ring
        · simp only [if_neg hS, ThresholdFunctions.expect_const]
  calc
    expect (fun z => ThresholdFunctions.disagreementProbability f
        (fun x => f (J.piecewise x z))) =
        expect (fun z => expect (fun x =>
          (1 / 2) * (1 - f x * f (J.piecewise x z)))) := by
      unfold ThresholdFunctions.disagreementProbability
      simp_rw [hindicator]
    _ = expect (fun x => expect (fun z =>
        (1 / 2) * (1 - f x * f (J.piecewise x z)))) := by
      simp_rw [expect_eq_fintypeExpect]
      exact Finset.expect_comm _ _ _
    _ = (1 / 2) *
        (1 - expect (fun x => f x * expect (fun z => f (J.piecewise x z)))) := by
      simp_rw [ThresholdFunctions.expect_const_mul, ThresholdFunctions.expect_sub,
        ThresholdFunctions.expect_const, ThresholdFunctions.expect_const_mul]
    _ = (1 / 2) * ((∑ S : Finset (Fin n), fourierCoeff f S ^ 2) -
        ∑ S : Finset (Fin n), if S ⊆ J then fourierCoeff f S ^ 2 else 0) := by
      rw [hcorrelation, parseval_pm_one f hf]
    _ = (1 / 2) * (∑ S : Finset (Fin n),
        if S ⊆ J then 0 else fourierCoeff f S ^ 2) := by
      congr 1
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro S _
      by_cases hS : S ⊆ J <;> simp [hS]
)

/-- Every ±1-valued cube function has a ±1-valued `J`-junta whose disagreement
probability is at most half its Fourier weight on sets not contained in `J`.
[OD14, Ex. 3.34; Thm. 9.28, proof]
This statement includes empty and full coordinate sets and the zero-dimensional cube.

**Proof sketch.** Choose a restriction of the coordinates outside `J` that minimizes
disagreement with the original function. Its disagreement is at most the uniform
average over all restrictions, which equals half the omitted Fourier weight by the
averaged disagreement identity. The restricted function remains ±1-valued and
depends only on the coordinates in `J`, so it is the required Boolean junta. -/
lemma exists_boolean_junta_of_fourier_omission {n : ℕ} (f : BooleanFunc n)
    (hf : isPmOne f) (J : Finset (Fin n)) :
    ∃ h : BooleanFunc n, isPmOne h ∧ KKL.IsJunta h J ∧
      ThresholdFunctions.disagreementProbability f h ≤
        (1 / 2) * (∑ S : Finset (Fin n),
          if S ⊆ J then 0 else fourierCoeff f S ^ 2) :=
  (by
  classical
  obtain ⟨z, _, hz⟩ := Finset.exists_min_image Finset.univ
    (fun z : BoolCube n => ThresholdFunctions.disagreementProbability f
      (fun x => f (J.piecewise x z))) Finset.univ_nonempty
  refine ⟨fun x => f (J.piecewise x z), ?_, ?_, ?_⟩
  · intro x
    exact hf (J.piecewise x z)
  · intro x y hxy
    apply congrArg f
    funext i
    by_cases hi : i ∈ J
    · rw [Finset.piecewise_eq_of_mem J x z hi,
        Finset.piecewise_eq_of_mem J y z hi]
      exact hxy i hi
    · rw [Finset.piecewise_eq_of_notMem J x z hi,
        Finset.piecewise_eq_of_notMem J y z hi]
  · calc
      ThresholdFunctions.disagreementProbability f (fun x => f (J.piecewise x z)) =
          expect (fun _ : BoolCube n =>
            ThresholdFunctions.disagreementProbability f
              (fun x => f (J.piecewise x z))) :=
        (ThresholdFunctions.expect_const _).symm
      _ ≤ expect (fun w => ThresholdFunctions.disagreementProbability f
          (fun x => f (J.piecewise x w))) :=
        ThresholdFunctions.expect_mono (fun w => hz w (by simp))
      _ = (1 / 2) * (∑ S : Finset (Fin n),
          if S ⊆ J then 0 else fourierCoeff f S ^ 2) :=
        expect_disagreement_coordinateRestriction f hf J
)


/-- Every ±1-valued cube function has a ±1-valued constant approximant whose
disagreement probability is at most half its variance.
[OD14, Ex. 3.34; §1.4]
This includes constant functions and the zero-dimensional cube.

**Proof sketch.** Apply Boolean junta rounding with the empty coordinate set.
The omitted Fourier sets are exactly the nonempty sets, whose squared
coefficients sum to the variance. -/
lemma exists_boolean_constant_approximation {n : ℕ} (f : BooleanFunc n)
    (hf : isPmOne f) :
    ∃ h : BooleanFunc n, isPmOne h ∧ KKL.IsJunta h ∅ ∧
      ThresholdFunctions.disagreementProbability f h ≤ (1 / 2) * cubeVariance f :=
  (by
  simpa [cubeVariance_eq_sum_nonempty_fourier] using
    exists_boolean_junta_of_fourier_omission f hf ∅
)

end BooleanAnalysis.Hypercontractivity
