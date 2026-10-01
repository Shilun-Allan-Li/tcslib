import TCSlib.BooleanAnalysis.Hypercontractivity.CubeDefinitions
import TCSlib.BooleanAnalysis.Hypercontractivity.Bonami
import TCSlib.BooleanAnalysis.ThresholdFunctions.Basic
import TCSlib.BooleanAnalysis.KKL

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Low-degree concentration and stable influences on the cube

## Main definitions

This file reuses cube norms, Walsh degree, stable influences, and Fourier weights.

## Main results

* `lowDegree_anticoncentration`: Theorem 9.7.
* `stableInfluence_one_third`, `stableInfluence_le`: Corollaries 9.12 and 9.25.
* `lowDegree_norm_ge_two`, `lowDegree_norm_le_two`: Theorems 9.21–9.22 for real exponents.
* `lowDegree_concentration`, `lowDegree_oneSided_anticoncentration`: Theorems 9.23–9.24.
* `level_k_inequality`, `level_one_inequality`: Fourier bounds for indicators.
* `stableCubeGraph_properties`: positivity, symmetry, regularity, and normalization.

The centered anticoncentration bound reuses the existing Bonami and Paley–Zygmund
proofs. The one-third corollary reuses the general stable-influence statement; the
remaining results are proof obligations.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014;
  May 2021 arXiv edition, Chapter 9, §§9.1–9.5 and Exercise 9.18.
-/

open scoped BigOperators Classical

namespace BooleanAnalysis.Hypercontractivity

/-- The stable cube has nonnegative symmetric weights, uniform outgoing mass, and unit
total mass for `-1 ≤ ρ ≤ 1`. [OD14, Rem. 9.11]

**Proof sketch.** Each coordinate kernel is nonnegative and symmetric with row sum one.
Factor the finite sums and multiply by the uniform mass. -/
theorem stableCubeGraph_properties (n : ℕ) (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1) 1) :
    (∀ x y, 0 ≤ (stableCubeGraph n ρ).edgeWeight x y) ∧
    (∀ x y, (stableCubeGraph n ρ).edgeWeight x y =
      (stableCubeGraph n ρ).edgeWeight y x) ∧
    (∀ x, ∑ y : BoolCube n, (stableCubeGraph n ρ).edgeWeight x y = uniformWeight n) ∧
    (∑ x : BoolCube n, ∑ y : BoolCube n, (stableCubeGraph n ρ).edgeWeight x y) = 1 := (by
  classical
  have hsum (x : BoolCube n) :
      ∑ y : BoolCube n, GeneralHypercontractivity.noiseKernel ρ x y = 1 := by
    unfold GeneralHypercontractivity.noiseKernel
    rw [← Fintype.prod_sum (fun (i : Fin n) (b : Bool) =>
      (1 + ρ * boolToSign (x i) * boolToSign b) / 2)]
    apply Finset.prod_eq_one
    intro i _
    norm_num [boolToSign]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y
    change 0 ≤ uniformWeight n * GeneralHypercontractivity.noiseKernel ρ x y
    refine mul_nonneg (by unfold uniformWeight; positivity) ?_
    unfold GeneralHypercontractivity.noiseKernel
    apply Finset.prod_nonneg
    intro i _
    cases x i <;> cases y i <;>
      norm_num [boolToSign] <;> linarith [hρ.1, hρ.2]
  · intro x y
    change uniformWeight n * GeneralHypercontractivity.noiseKernel ρ x y =
      uniformWeight n * GeneralHypercontractivity.noiseKernel ρ y x
    congr 1
    unfold GeneralHypercontractivity.noiseKernel
    apply Finset.prod_congr rfl
    intro i _
    ring
  · intro x
    change (∑ y : BoolCube n,
      uniformWeight n * GeneralHypercontractivity.noiseKernel ρ x y) = _
    rw [← Finset.mul_sum, hsum, mul_one]
  · change (∑ x : BoolCube n, ∑ y : BoolCube n,
      uniformWeight n * GeneralHypercontractivity.noiseKernel ρ x y) = 1
    simp_rw [← Finset.mul_sum, hsum]
    simpa only [expect] using
      (ThresholdFunctions.expect_const (n := n) (1 : ℝ))
)

/-- A nonconstant degree-`k` cube function deviates from its mean by more than half its
standard deviation with probability at least `9^(1-k)/16`. [OD14, Thm. 9.7]
Positive variance expresses nonconstancy; the fraction avoids natural exponent subtraction.

**Proof sketch.** Center the function, apply the Bonami fourth-moment bound, and apply
Paley–Zygmund at half its second norm. -/
theorem lowDegree_anticoncentration {n k : ℕ} (f : BooleanFunc n)
    (hdeg : has_degree_at_most f k) (hvar : 0 < cubeVariance f) :
    9 / (16 * (9 : ℝ) ^ k) ≤
      cubeProbability (fun x => Real.sqrt (cubeVariance f) / 2 < |f x - expect f|) := by
  classical
  let g : BooleanFunc n := fun x => f x - expect f
  -- Centering changes only the empty Fourier coefficient, so preserves the degree bound.
  have hgdeg : has_degree_at_most g k := by
    intro S hS
    by_cases hcard : S.card ≤ k
    · exact hcard
    · have hSne : S ≠ ∅ := by
        intro h
        subst S
        simp at hcard
      have hfS : fourierCoeff f S = 0 := by
        by_contra h
        exact hcard (hdeg S h)
      have hmeanS : expect (chiS S) = 0 := by
        have h := fourier_coeff_chi (∅ : Finset (Fin n)) S
        simpa only [innerProduct, chiS_empty, one_mul,
          if_neg (Ne.symm hSne)] using h
      have hcoeff : fourierCoeff g S = fourierCoeff f S := by
        simp only [g, fourierCoeff, innerProduct, sub_mul,
          ThresholdFunctions.expect_sub, ThresholdFunctions.expect_const_mul,
          hmeanS, mul_zero, sub_zero]
      exact False.elim (hS (hcoeff.trans hfS))
  have hm2 : ProbabilityTheory.moment g 2 (Bonami.uniformMeasure n) =
      cubeVariance f := by
    rw [Bonami.moment_eq_expect g 2 (Bonami.uniformMeasure n)
      Bonami.uniformMeasure_apply]
    rfl
  -- Identify the finite indicator expectation with probability under the existing measure.
  have hprob (A : BoolCube n → Prop) :
      ((Bonami.uniformMeasure n) {x | A x}).toReal = cubeProbability A := by
    have hset : {x | A x} =
        (Finset.univ.filter A : Set (BoolCube n)) := by
      ext x
      simp
    change (Bonami.uniformMeasure n).real {x | A x} = _
    rw [hset, ← MeasureTheory.sum_measureReal_singleton]
    simp only [MeasureTheory.measureReal_def, Bonami.uniformMeasure_apply]
    rw [Finset.sum_filter]
    unfold cubeProbability cubeIndicator expect
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : A x <;> simp [Set.indicator_apply, hx]
  have hb := Bonami.b_reasonable_anticon_zero
    (Bonami.bonami_lemma k g hgdeg) (measurable_of_finite g)
    MeasureTheory.Integrable.of_finite MeasureTheory.Integrable.of_finite
    (by rw [hm2]; exact hvar)
    (t := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  rw [hm2] at hb
  -- At t=1/2 the squared Paley–Zygmund event is the stated strict deviation event.
  have hevent :
      {x : BoolCube n | (1 / 2 : ℝ) ^ 2 * cubeVariance f < g x ^ 2} =
        {x : BoolCube n |
          Real.sqrt (cubeVariance f) / 2 < |f x - expect f|} := by
    ext x
    simp only [Set.mem_setOf_eq]
    have hsq : (Real.sqrt (cubeVariance f) / 2) ^ 2 =
        (1 / 2 : ℝ) ^ 2 * cubeVariance f := by
      rw [div_pow, Real.sq_sqrt hvar.le]
      ring
    rw [← hsq, sq_lt_sq, abs_of_nonneg (by positivity)]
  rw [hevent, hprob] at hb
  convert hb using 1 <;>
    norm_num [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm] <;> ring

/-- Every finite real `q ≥ 2` gives `‖f‖q ≤ (√(q-1))^k ‖f‖₂` for degree at most `k`.
[OD14, Thm. 9.21]

**Proof sketch.** Apply `(2,q)`-hypercontractivity to the inverse-noise rescaling of the
function. Parseval bounds its squared norm by `(q-1)^k` times the original squared norm. -/
theorem lowDegree_norm_ge_two {n k : ℕ} (f : BooleanFunc n)
    (hdeg : has_degree_at_most f k) (q : ℝ) (hq : 2 ≤ q) :
    cubeLpNorm q f ≤ Real.sqrt (q - 1) ^ k * l2Norm f := sorry

/-- Every real `1 ≤ p ≤ 2` gives `‖f‖₂ ≤ exp((2/p-1)k) ‖f‖p` for degree at most `k`.
[OD14, Thm. 9.22]

**Proof sketch.** Interpolate the `p`-norm and a `(2+η)`-norm with Hölder, bound the latter
by hypercontractivity, cancel the second norm, and let `η` decrease to zero. -/
theorem lowDegree_norm_le_two {n k : ℕ} (f : BooleanFunc n)
    (hdeg : has_degree_at_most f k) (p : ℝ) (hp : p ∈ Set.Icc 1 2) :
    l2Norm f ≤ Real.exp ((2 / p - 1) * (k : ℝ)) * cubeLpNorm p f := sorry

/-- For positive `k` and nonzero degree-`k` functions, the tail above `t‖f‖₂` is at most
`exp(-k t^(2/k)/(2e))` for `t ≥ (√(2e))^k`. [OD14, Thm. 9.23]
The positivity assumptions expose the source proof's normalization and reciprocal degree;
the printed non-strict event is false for the zero function.

**Proof sketch.** Apply Markov to the `q`th moment, use the degree estimate, and choose
`q = t^(2/k)/e`, which is at least two. -/
theorem lowDegree_concentration {n k : ℕ} (f : BooleanFunc n) (hk : 0 < k)
    (hdeg : has_degree_at_most f k) (hf : 0 < l2Norm f)
    (t : ℝ) (ht : Real.sqrt (2 * Real.exp 1) ^ k ≤ t) :
    cubeProbability (fun x => t * l2Norm f ≤ |f x|) ≤
      Real.exp (-(k : ℝ) / (2 * Real.exp 1) * t ^ (2 / (k : ℝ))) := sorry

/-- A nonconstant degree-`k` function exceeds its mean with probability at least
`exp(-2k)/4`. [OD14, Thm. 9.24]

**Proof sketch.** Center the function. Its positive part has expectation half its first
norm. Apply Cauchy–Schwarz to that part, then the low-degree first-to-second-norm bound. -/
theorem lowDegree_oneSided_anticoncentration {n k : ℕ} (f : BooleanFunc n)
    (hdeg : has_degree_at_most f k) (hvar : 0 < cubeVariance f) :
    Real.exp (-2 * (k : ℝ)) / 4 ≤ cubeProbability (fun x => expect f < f x) := sorry

/-- Stable influence at `ρ ∈ [0,1]` is at most ordinary influence to the power
`2/(1+ρ)` for Boolean functions. [OD14, Cor. 9.25]

**Proof sketch.** Apply `(1+ρ,2)`-hypercontractivity to the coordinate derivative and
evaluate its norm using its `{-1,0,1}`-valued range. -/
theorem stableInfluence_le {n : ℕ} (f : BooleanFunc n) (hf : isPmOne f)
    (i : Fin n) (ρ : ℝ) (hρ : ρ ∈ Set.Icc 0 1) :
    KKL.noisyInfluence ρ i f ≤ (influence i f) ^ (2 / (1 + ρ)) := sorry

/-- The one-third-stable influence of a Boolean function is at most its ordinary influence
to the power `3/2`. [OD14, Cor. 9.12]

**Proof sketch.** Specialize the general stable-influence bound to `ρ=1/3` and
simplify the exponent `2/(1+ρ)` to `3/2`. -/
theorem stableInfluence_one_third {n : ℕ} (f : BooleanFunc n) (hf : isPmOne f) (i : Fin n) :
    KKL.noisyInfluence (1 / 3) i f ≤ (influence i f) ^ (3 / 2 : ℝ) := by
  convert stableInfluence_le f hf i (1 / 3) (by norm_num) using 1 <;> norm_num

/-- For an indicator of positive mean `α` and `1 ≤ k ≤ 2 ln(1/α)`, its Fourier weight
through level `k` is at most `((2e/k) ln(1/α))^k α²`.
[OD14, §9.5, Level-k Inequalities] The zero indicator is excluded from the logarithmic formula.

**Proof sketch.** Small-set expansion bounds the weight by `ρ^(-k) α^(2/(1+ρ))`.
Weaken the exponent to `2(1-ρ)` and set `ρ = k/(2 ln(1/α))`. -/
theorem level_k_inequality {n k : ℕ} (f : BooleanFunc n)
    (hf : ∀ x, f x = 0 ∨ f x = 1) (hα : 0 < expect f) (hk : 0 < k)
    (hkα : (k : ℝ) ≤ 2 * Real.log (1 / expect f)) :
    ThresholdFunctions.fourierWeightUpTo k f ≤
      ((2 * Real.exp 1 / (k : ℝ)) * Real.log (1 / expect f)) ^ k * (expect f) ^ 2 := sorry

/-- An indicator of positive mean `α` has level-one Fourier weight at most
`2α² ln(1/α)`. [OD14, §9.5 and Ex. 9.18(b)]

**Proof sketch.** Use the subgaussian exponential moment bound for the normalized
degree-one part, and optimize its exponential parameter on the indicator's support. -/
theorem level_one_inequality {n : ℕ} (f : BooleanFunc n)
    (hf : ∀ x, f x = 0 ∨ f x = 1) (hα : 0 < expect f) :
    weightLevel 1 f ≤ 2 * (expect f) ^ 2 * Real.log (1 / expect f) := sorry

end BooleanAnalysis.Hypercontractivity
