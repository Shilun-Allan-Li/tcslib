/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.BooleanAnalysis.Hypercontractivity.CubeDefinitions
import TCSlib.BooleanAnalysis.ThresholdFunctions.Basic
import TCSlib.BooleanAnalysis.KKL
import TCSlib.BooleanAnalysis.Switching.Circuit

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Full KKL and exponential junta statements

## Main definitions

No new definitions. Boolean approximants on the original cube depend only on a small set
of coordinates, implementing the cylinder extension of a junta.

## Main results

* `kkl`, `kkl_edgeIsoperimetric`: full variance-scaled KKL and its explicit stronger bound.
* `lowInfluence_fourierConcentration`: Theorem 9.28, with its approximation consequence.
* `friedgut_junta`: the dimension-independent exponential junta theorem.
* `dnf_junta`, `linearThreshold_junta`, `exists_large_nonempty_fourierCoeff`: 9.30–9.32.

These skeletons supplement the existing KKL file without changing its declarations.
Every hidden asymptotic constant is quantified before the dimension, function, and accuracy.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014;
  May 2021 arXiv edition, §9.6, Theorem 9.28, Friedgut's Junta Theorem, Corollaries 9.30–9.32.
-/

open scoped BigOperators Classical

namespace BooleanAnalysis.Hypercontractivity

/-- A universal positive constant bounds maximum influence below by
`c Var[f] ln(n)/n` for every Boolean cube function. [OD14, §9.6, KKL Theorem]
Changing binary to natural logarithms is absorbed into the constant. The reused maximum
uses absolute influences, equal to influences by nonnegativity; dimension zero is harmless.

**Proof sketch.** If normalized total influence is at least a small multiple of `ln(n)`,
average the influences. Otherwise use the exponential edge-isoperimetric bound. -/
theorem kkl : ∃ c : ℝ, 0 < c ∧ ∀ (n : ℕ) (f : BooleanFunc n), isPmOne f →
    c * cubeVariance f * (Real.log (n : ℝ) / (n : ℝ)) ≤
      ThresholdFunctions.maxInfluence f := sorry

/-- A nonconstant Boolean function has maximum influence at least `(9/Ĩ²) 9^(-Ĩ)`,
where `Ĩ=I[f]/Var[f]`. [OD14, §9.6, KKL Edge-Isoperimetric Theorem]

**Proof sketch.** Normalize the nonempty Fourier weights to a distribution and apply
Jensen to `3^(-|S|)`. Bound the stable influence sum using Corollary 9.12 and the square
root of maximum influence, then square and rearrange. -/
theorem kkl_edgeIsoperimetric {n : ℕ} (f : BooleanFunc n) (hf : isPmOne f)
    (hvar : 0 < cubeVariance f) :
    let I := totalInfluence f / cubeVariance f
    (9 / I ^ 2) * (9 : ℝ) ^ (-I) ≤ ThresholdFunctions.maxInfluence f := sorry

/-- Coordinates of influence at least `ε² 9^(-k)/I[f]²` capture all but `ε` of the
degree-at-most-`k` Fourier weight and number at most `I[f]³ 9^k/ε²`. A tail bound of `ε`
then gives an `ε`-close Boolean junta on those coordinates. [OD14, Thm. 9.28]
For constants the threshold is set to one, making the coordinate set empty and resolving
the source's division by zero.

**Proof sketch.** Sum one-third-stable influences over omitted coordinates and use the
degree cutoff. Add the high-degree tail, then use the randomized-rounding argument of
Exercise 3.34 to obtain a Boolean approximant with half the spectral error. -/
theorem lowInfluence_fourierConcentration {n : ℕ} (f : BooleanFunc n) (hf : isPmOne f)
    (ε : ℝ) (hε : ε ∈ Set.Ioc 0 1) (k : ℕ) :
    let τ := if totalInfluence f = 0 then 1
      else ε ^ 2 / (totalInfluence f) ^ 2 / (9 : ℝ) ^ k
    let J := KKL.influentialCoords f τ
    (J.card : ℝ) ≤ (totalInfluence f) ^ 3 / ε ^ 2 * (9 : ℝ) ^ k ∧
    (∑ S : Finset (Fin n),
      if S.card ≤ k ∧ ¬ (S ⊆ J) then fourierCoeff f S ^ 2 else 0) ≤ ε ∧
    (ThresholdFunctions.fourierWeightAbove k f ≤ ε →
      (∑ S : Finset (Fin n),
        if S ⊆ J ∧ S.card ≤ k then 0 else fourierCoeff f S ^ 2) ≤ 2 * ε ∧
      ∃ h : BooleanFunc n, isPmOne h ∧ KKL.IsJunta h J ∧ ThresholdFunctions.IsClose f h ε) :=
  sorry

/-- Every Boolean function is `ε`-close to a junta on at most `exp(C I[f]/ε)` coordinates
for an absolute `C`; the same set captures all but `2ε` of its Fourier weight at degrees
at most `I[f]/ε`. [OD14, §9.6, Friedgut's Junta Theorem]
The junta bound is independent of ambient dimension.

**Proof sketch.** Bound the Fourier tail by total influence and apply Theorem 9.28.
Absorb the polynomial factor into the exponential; sufficiently small influence permits
a constant approximation. -/
theorem friedgut_junta : ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (f : BooleanFunc n), isPmOne f → ∀ ε : ℝ, ε ∈ Set.Ioc 0 1 →
      ∃ (J : Finset (Fin n)) (h : BooleanFunc n),
        (J.card : ℝ) ≤ Real.exp (C * totalInfluence f / ε) ∧
        (∑ S : Finset (Fin n), if S ⊆ J ∧ (S.card : ℝ) ≤ totalInfluence f / ε
          then 0 else fourierCoeff f S ^ 2) ≤ 2 * ε ∧
        isPmOne h ∧ KKL.IsJunta h J ∧ ThresholdFunctions.IsClose f h ε := sorry

/-- A width-`w` DNF is `ε`-close to a junta on at most `(1/ε)^(Cw)` coordinates for an
absolute `C`. The sign encoding sends true to `-1`. [OD14, Cor. 9.30]

**Proof sketch.** Use the DNF Fourier-tail bound at degree `O(w log(1/ε))`, then apply
the optimized stable-influence junta bound. Constant approximation covers large errors
and width-zero formulas. -/
theorem dnf_junta : ∃ C : ℝ, 0 < C ∧
    ∀ (n w : ℕ) (d : DNF n), d.width ≤ w → ∀ ε : ℝ, ε ∈ Set.Ioc 0 1 →
      ∃ (J : Finset (Fin n)) (h : BooleanFunc n),
        (J.card : ℝ) ≤ (1 / ε) ^ (C * (w : ℝ)) ∧ isPmOne h ∧ KKL.IsJunta h J ∧
        ThresholdFunctions.IsClose (fun x => boolToSign (d.eval x)) h ε := sorry

/-- An LTF is `ε`-close to a junta on at most `I[f]^(2+η) (1/η)^(C/ε²)` coordinates
for an absolute `C` and `0 < ε,η ≤ 1/2`. [OD14, Cor. 9.31]

**Proof sketch.** Peres's theorem gives Fourier concentration at degree `O(1/ε²)`.
Use that cutoff in Remark 9.29's optimized junta bound and absorb the remaining factors
into the power of `1/η`. -/
theorem linearThreshold_junta : ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (f : BooleanFunc n), isPmOne f → ThresholdFunctions.IsLinearThreshold f →
      ∀ ε η : ℝ, ε ∈ Set.Ioc 0 (1 / 2) → η ∈ Set.Ioc 0 (1 / 2) →
      ∃ (J : Finset (Fin n)) (h : BooleanFunc n),
        (J.card : ℝ) ≤ (totalInfluence f) ^ (2 + η) * (1 / η) ^ (C / ε ^ 2) ∧
        isPmOne h ∧ KKL.IsJunta h J ∧ ThresholdFunctions.IsClose f h ε := sorry

/-- A Boolean function with variance at least one half has a nonempty Fourier coefficient
on at most `C I[f]` coordinates whose square is at least `exp(-C I[f]²)`.
[OD14, Cor. 9.32] A single absolute constant covers both asymptotic terms.

**Proof sketch.** Apply Friedgut's theorem with error `1/8`. At least a quarter of the
Fourier weight lies on nonempty retained sets. Count them and apply the pigeonhole principle. -/
theorem exists_large_nonempty_fourierCoeff : ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (f : BooleanFunc n), isPmOne f → (1 / 2 : ℝ) ≤ cubeVariance f →
      ∃ S : Finset (Fin n), S.Nonempty ∧ (S.card : ℝ) ≤ C * totalInfluence f ∧
        Real.exp (-C * (totalInfluence f) ^ 2) ≤ fourierCoeff f S ^ 2 := sorry

end BooleanAnalysis.Hypercontractivity
