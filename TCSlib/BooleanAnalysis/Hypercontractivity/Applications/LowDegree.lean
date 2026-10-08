/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import TCSlib.BooleanAnalysis.Hypercontractivity.Cube.Definitions
import TCSlib.BooleanAnalysis.Hypercontractivity.Cube.Bonami
import TCSlib.BooleanAnalysis.Hypercontractivity.Applications.SmallSetExpansion
import TCSlib.BooleanAnalysis.ThresholdFunctions.Basic
import TCSlib.BooleanAnalysis.ThresholdFunctions.DegreeOne
import TCSlib.BooleanAnalysis.ThresholdFunctions.LowDegreeNorm
import TCSlib.BooleanAnalysis.ThresholdFunctions.LinearThresholdInfluence
import TCSlib.BooleanAnalysis.KKL

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Low-degree and stable-cube consequences

Spectral, anticoncentration, and concentration applications of cube hypercontractivity.

## Main definitions

Shared definitions are imported; local technical helpers accompany their proofs.

## Main results

* `lowDegree_l1_l2_sq`.
* `stableCubeGraph_properties`.
* `lowDegree_anticoncentration`.
* `lowDegree_norm_ge_two`.
* `lowDegree_norm_le_two`.
* `lowDegree_concentration`.
* `lowDegree_oneSided_anticoncentration`.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014, §§9.1–9.5.
-/

open BooleanAnalysis MeasureTheory Set Filter ProbabilityTheory Real
open scoped BigOperators ENNReal Classical

namespace BooleanAnalysis.Hypercontractivity


/-- A cube function of degree at most `k` has squared second norm at most `exp(2k)`
times the square of its expected absolute value. [OD14, Thm. 9.22, endpoint `p=1`]
The inequality is rearranged to avoid division and square roots.

**Proof sketch.** Apply the existing polynomial norm bound to the Walsh coefficients.
Walsh expansion identifies its evaluation with the original function, and Parseval
identifies the squared coefficient norm with its squared second norm. -/
lemma lowDegree_l1_l2_sq {n k : ℕ} (f : BooleanFunc n)
    (hdeg : has_degree_at_most f k) :
    Real.exp (-2 * (k : ℝ)) * innerProduct f f ≤
      (expect (fun x => |f x|)) ^ 2 := (by
  let p : ThresholdFunctions.MultilinearPolynomial n := fourierCoeff f
  have hp : p.HasDegreeAtMost k := by
    intro S hS
    by_contra h
    exact (not_lt_of_ge (hdeg S h)) hS
  have heval : p.eval = f := by
    funext x
    exact (walsh_expansion f x).symm
  have h := ThresholdFunctions.low_degree_l1_l2_sq p hp
  rw [heval] at h
  simpa only [p, ← parseval f] using h
)

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
      ∑ y : BoolCube n, noiseKernel ρ x y = 1 := by
    unfold noiseKernel
    rw [← Fintype.prod_sum (fun (i : Fin n) (b : Bool) =>
      (1 + ρ * boolToSign (x i) * boolToSign b) / 2)]
    apply Finset.prod_eq_one
    intro i _
    norm_num [boolToSign]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y
    change 0 ≤ uniformWeight n * noiseKernel ρ x y
    refine mul_nonneg (by unfold uniformWeight; positivity) ?_
    unfold noiseKernel
    apply Finset.prod_nonneg
    intro i _
    cases x i <;> cases y i <;>
      norm_num [boolToSign] <;> linarith [hρ.1, hρ.2]
  · intro x y
    change uniformWeight n * noiseKernel ρ x y =
      uniformWeight n * noiseKernel ρ y x
    congr 1
    unfold noiseKernel
    apply Finset.prod_congr rfl
    intro i _
    ring
  · intro x
    change (∑ y : BoolCube n,
      uniformWeight n * noiseKernel ρ x y) = _
    rw [← Finset.mul_sum, hsum, mul_one]
  · change (∑ x : BoolCube n, ∑ y : BoolCube n,
      uniformWeight n * noiseKernel ρ x y) = 1
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
  have hm2 : ProbabilityTheory.moment g 2 (uniformMeasure n) =
      cubeVariance f := by
    rw [moment_eq_expect g 2 (uniformMeasure n)
      uniformMeasure_apply]
    rfl
  -- Identify the finite indicator expectation with probability under the existing measure.
  have hprob (A : BoolCube n → Prop) :
      ((uniformMeasure n) {x | A x}).toReal = cubeProbability A := by
    have hset : {x | A x} =
        (Finset.univ.filter A : Set (BoolCube n)) := by
      ext x
      simp
    change (uniformMeasure n).real {x | A x} = _
    rw [hset, ← MeasureTheory.sum_measureReal_singleton]
    simp only [MeasureTheory.measureReal_def, uniformMeasure_apply]
    rw [Finset.sum_filter]
    unfold cubeProbability cubeIndicator expect
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : A x <;> simp [Set.indicator_apply, hx]
  have hb := b_reasonable_anticon_zero
    (bonami_lemma k g hgdeg) (measurable_of_finite g)
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
    cubeLpNorm q f ≤ Real.sqrt (q - 1) ^ k * l2Norm f := (by
  let r : ℝ := Real.sqrt (q - 1)
  have hr : 1 ≤ r := Real.one_le_sqrt.mpr (by linarith)
  have hcancel : noiseOp (1 / r) (noiseOp r f) = f := by
    rw [noiseOp_compose,
      one_div_mul_cancel (ne_of_gt (lt_of_lt_of_le zero_lt_one hr))]
    funext x
    simpa only [noiseOp, one_pow, one_mul] using (walsh_expansion f x).symm
  have hc := general_one_function_hypercontractivity
    2 q (by norm_num) hq (by linarith) (1 / r) (by positivity)
    (div_le_one_of_le₀ hr (by linarith))
    (by norm_num [r, Real.sqrt_div (show (0 : ℝ) ≤ 1 by norm_num)])
    (noiseOp r f)
  calc
    cubeLpNorm q f ≤ l2Norm (noiseOp r f) := by
      simpa only [hcancel, cubeLpNorm, Real.rpow_two, pow_two,
        abs_mul_abs_self, ← Real.sqrt_eq_rpow, l2Norm, innerProduct] using hc
    _ ≤ Real.sqrt (q - 1) ^ k * l2Norm f := l2Norm_noiseOp_le f hdeg r hr
)

/-- For `0 < p < 2 < q`, a cube function of Fourier degree at most `k` satisfies
`‖f‖₂ ≤ exp(k q (2-p)/(2p)) ‖f‖p`.
[OD14, Thm. 9.22 (proof)] This intermediate estimate is stated for every positive
`p < 2`; the main theorem uses `1 ≤ p < 2` and lets `q` decrease to two.

**Proof sketch.** The upper hypercontractive degree bound gives
`‖f‖q ≤ (√(q-1))^k ‖f‖₂`. The inequality `log(q-1) ≤ q-2` bounds its coefficient
by `exp(k(q-2)/2)`. Apply the general norm interpolation bound with this exponential
coefficient and simplify its exponent to `k q (2-p)/(2p)`. -/
private lemma lowDegree_norm_le_two_aux {n k : ℕ} (f : BooleanFunc n)
    (hdeg : has_degree_at_most f k) (p q : ℝ)
    (hp : 0 < p) (hp2 : p < 2) (hq2 : 2 < q) :
    l2Norm f ≤
      Real.exp ((k : ℝ) * q * (2 - p) / (2 * p)) * cubeLpNorm p f :=
  (by
  let c : ℝ := (k : ℝ) * (q - 2) / 2
  have hqm1 : 0 < q - 1 := by linarith
  have hfactor : Real.sqrt (q - 1) ^ k ≤ Real.exp c := by
    rw [← Real.rpow_natCast _ k,
      Real.rpow_def_of_pos (Real.sqrt_pos.mpr hqm1), Real.log_sqrt hqm1.le]
    apply Real.exp_le_exp.mpr
    have hl := mul_le_mul_of_nonneg_right
      (Real.log_le_sub_one_of_pos hqm1) (Nat.cast_nonneg k)
    dsimp [c]
    nlinarith only [hl]
  have hb : cubeLpNorm q f ≤ Real.exp c * l2Norm f :=
    (lowDegree_norm_ge_two f hdeg q hq2.le).trans
      (mul_le_mul_of_nonneg_right hfactor (Real.sqrt_nonneg _))
  have hi := cube_norm_interpolation_bound f p q c hp hp2 hq2 hb
  have hexp : c * q * (2 - p) / (p * (q - 2)) =
      (k : ℝ) * q * (2 - p) / (2 * p) := by
    dsimp [c]
    field_simp [hp.ne', (sub_pos.mpr hq2).ne']
  simpa only [hexp] using hi
)

/-- Every real `1 ≤ p ≤ 2` gives `‖f‖₂ ≤ exp((2/p-1)k) ‖f‖p` for degree at most `k`.
[OD14, Thm. 9.22]

**Proof sketch.** Interpolate the `p`-norm and a `(2+η)`-norm with Hölder, bound the latter
by hypercontractivity, cancel the second norm, and let `η` decrease to zero. -/
theorem lowDegree_norm_le_two {n k : ℕ} (f : BooleanFunc n)
    (hdeg : has_degree_at_most f k) (p : ℝ) (hp : p ∈ Set.Icc 1 2) :
    l2Norm f ≤ Real.exp ((2 / p - 1) * (k : ℝ)) * cubeLpNorm p f := (by
  by_cases hp2 : p = 2
  · subst p
    simp [cubeLpNorm, Real.sqrt_eq_rpow, pow_two, abs_mul_abs_self, l2Norm, innerProduct]
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp.1
  have hp2' : p < 2 := lt_of_le_of_ne hp.2 hp2
  let B : ℝ → ℝ := fun q =>
    Real.exp ((k : ℝ) * q * (2 - p) / (2 * p)) * cubeLpNorm p f
  have hcontinuous : Continuous B := by
    dsimp [B]
    fun_prop
  have ht : Filter.Tendsto B
      (nhdsWithin (2 : ℝ) (Set.Ioi 2)) (nhds (B 2)) :=
    hcontinuous.continuousAt.continuousWithinAt.tendsto
  have hlim : l2Norm f ≤ B 2 := ge_of_tendsto ht
    (Filter.Eventually.mono self_mem_nhdsWithin
      (fun q hq => lowDegree_norm_le_two_aux f hdeg p q hp0 hp2' hq))
  have he : (k : ℝ) * 2 * (2 - p) / (2 * p) =
      (2 / p - 1) * (k : ℝ) := by
    calc
      _ = (k : ℝ) * ((2 - p) / p) := by field_simp [hp0.ne']
      _ = _ := by
        rw [sub_div, div_self hp0.ne']
        ring
  simpa only [B, he] using hlim
)

/-- For positive `k`, the threshold `t ≥ (√(2e)) ^ k` implies `t > 0`
and makes the concentration parameter `t ^ (2 / k) / e` at least two.
[OD14, Thm. 9.23 (proof)]

**Proof sketch.** The threshold is positive, so `t` is positive.
Raise the threshold inequality to the positive power `2 / k`;
the lower bound becomes `2e`. Divide by the positive number `e`. -/
private lemma concentration_parameter {k : ℕ} (hk : 0 < k) (t : ℝ)
    (ht : Real.sqrt (2 * Real.exp 1) ^ k ≤ t) :
    0 < t ∧ 2 ≤ t ^ (2 / (k : ℝ)) / Real.exp 1 := (by
  have hs : 0 < Real.sqrt (2 * Real.exp 1) :=
    Real.sqrt_pos.mpr (by positivity)
  have ht0 : 0 < t := lt_of_lt_of_le (pow_pos hs k) ht
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  refine ⟨ht0, ?_⟩
  have hpow := Real.rpow_le_rpow (pow_pos hs k).le ht
    (by positivity : 0 ≤ 2 / (k : ℝ))
  rw [← Real.rpow_natCast _ k, ← Real.rpow_mul hs.le,
    mul_div_cancel₀ 2 hkR.ne', Real.rpow_two, Real.sq_sqrt (by positivity)] at hpow
  exact (le_div_iff₀ (Real.exp_pos 1)).mpr hpow
)

/-- For positive degree `k` and threshold `t`, the optimizing moment exponent
`q = t ^ (2 / k) / e` gives
`((√q) ^ k / t) ^ q = exp(-k t ^ (2 / k) / (2e))`.
[OD14, Thm. 9.23 (proof)]

**Proof sketch.** The exponent `q` is positive and satisfies
`log q = (2 / k) log t - 1`. Thus the logarithm of `(√q) ^ k / t`
is `-k / 2`. Express the real power through the exponential, substitute
the chosen value of `q`, and simplify. -/
private lemma concentration_optimized_moment {k : ℕ} (hk : 0 < k)
    (t : ℝ) (ht : 0 < t) :
    let q : ℝ := t ^ (2 / (k : ℝ)) / Real.exp 1
    (Real.sqrt q ^ k / t) ^ q =
      Real.exp (-(k : ℝ) / (2 * Real.exp 1) * t ^ (2 / (k : ℝ))) :=
  (by
  let q : ℝ := t ^ (2 / (k : ℝ)) / Real.exp 1
  change (Real.sqrt q ^ k / t) ^ q =
    Real.exp (-(k : ℝ) / (2 * Real.exp 1) * t ^ (2 / (k : ℝ)))
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have hq : 0 < q := div_pos (Real.rpow_pos_of_pos ht _) (Real.exp_pos _)
  have hlogq : Real.log q = (2 / (k : ℝ)) * Real.log t - 1 := by
    dsimp [q]
    rw [Real.log_div (Real.rpow_pos_of_pos ht _).ne' (Real.exp_pos _).ne',
      Real.log_rpow ht, Real.log_exp]
  have hratio : Real.log (Real.sqrt q ^ k / t) = -(k : ℝ) / 2 := by
    rw [Real.log_div (pow_pos (Real.sqrt_pos.mpr hq) k).ne' ht.ne',
      Real.log_pow, Real.log_sqrt hq.le, hlogq]
    field_simp [hkR.ne']
    ring
  rw [Real.rpow_def_of_pos (div_pos (pow_pos (Real.sqrt_pos.mpr hq) k) ht),
    hratio]
  congr 1
  dsimp [q]
  field_simp
)

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
      Real.exp (-(k : ℝ) / (2 * Real.exp 1) * t ^ (2 / (k : ℝ))) := (by
  obtain ⟨ht0, hq2⟩ := concentration_parameter hk t ht
  let q : ℝ := t ^ (2 / (k : ℝ)) / Real.exp 1
  have hq : 0 < q := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hq2
  have hnorm : cubeLpNorm q f ≤ Real.sqrt q ^ k * l2Norm f :=
    (lowDegree_norm_ge_two f hdeg q hq2).trans
      (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (Real.sqrt_nonneg _)
          (Real.sqrt_le_sqrt (by linarith)) k) hf.le)
  have hratio : cubeLpNorm q f / (t * l2Norm f) ≤ Real.sqrt q ^ k / t := by
    calc
      _ ≤ (Real.sqrt q ^ k * l2Norm f) / (t * l2Norm f) :=
        div_le_div_of_nonneg_right hnorm (mul_pos ht0 hf).le
      _ = _ := mul_div_mul_right _ _ hf.ne'
  calc
    cubeProbability (fun x => t * l2Norm f ≤ |f x|) ≤
        (cubeLpNorm q f / (t * l2Norm f)) ^ q :=
      cubeProbability_le_cubeLpNorm_div_rpow f q (t * l2Norm f) hq (mul_pos ht0 hf)
    _ ≤ (Real.sqrt q ^ k / t) ^ q :=
      Real.rpow_le_rpow
        (div_nonneg (Real.rpow_nonneg
          (expect_rpow_abs_nonneg q f) _) (mul_pos ht0 hf).le)
        hratio hq.le
    _ = _ := concentration_optimized_moment hk t ht0
)

/-- A nonconstant degree-`k` function exceeds its mean with probability at least
`exp(-2k)/4`. [OD14, Thm. 9.24]

**Proof sketch.** Center the function. Its positive part has expectation half its first
norm. Apply Cauchy–Schwarz to that part, then the low-degree first-to-second-norm bound. -/
theorem lowDegree_oneSided_anticoncentration {n k : ℕ} (f : BooleanFunc n)
    (hdeg : has_degree_at_most f k) (hvar : 0 < cubeVariance f) :
    Real.exp (-2 * (k : ℝ)) / 4 ≤ cubeProbability (fun x => expect f < f x) := (by
  let g : BooleanFunc n := fun x => f x - expect f
  have hmean : expect g = 0 := by
    simp only [g, ThresholdFunctions.expect_sub,
      ThresholdFunctions.expect_const, sub_self]
  have h := (lowDegree_l1_l2_sq g
    (has_degree_at_most_sub_const f hdeg (expect f))).trans
    (centered_abs_expect_sq_le g hmean)
  have hsecond : innerProduct g g = cubeVariance f := by
    simp only [g, innerProduct, cubeVariance, pow_two]
  rw [hsecond] at h
  simp only [g, sub_pos] at h
  apply (div_le_iff₀ (by norm_num : 0 < (4 : ℝ))).2
  apply (mul_le_mul_iff_right₀ hvar).mp
  convert h using 1 <;> ring
)

end BooleanAnalysis.Hypercontractivity
