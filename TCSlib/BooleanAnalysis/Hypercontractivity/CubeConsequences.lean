import TCSlib.BooleanAnalysis.Hypercontractivity.CubeDefinitions
import TCSlib.BooleanAnalysis.Hypercontractivity.Bonami
import TCSlib.BooleanAnalysis.Hypercontractivity.Applications
import TCSlib.BooleanAnalysis.ThresholdFunctions.Basic
import TCSlib.BooleanAnalysis.ThresholdFunctions.DegreeOne
import TCSlib.BooleanAnalysis.ThresholdFunctions.LowDegreeNorm
import TCSlib.BooleanAnalysis.ThresholdFunctions.LinearThresholdInfluence
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
* `lowDegree_l1_l2_sq`: the squared first-to-second-norm endpoint of Theorem 9.22.
* `lowDegree_concentration`, `lowDegree_oneSided_anticoncentration`: Theorems 9.23–9.24.
* `level_k_inequality`, `level_one_inequality`: Fourier bounds for indicators.
* `stableCubeGraph_properties`: positivity, symmetry, regularity, and normalization.

The centered anticoncentration bound reuses the existing Bonami and Paley–Zygmund
proofs. The squared first-to-second-norm endpoint transfers the existing polynomial
bound through Walsh expansion and Parseval. The indicator correlation estimate
reuses the Rademacher exponential-moment bound and the conditional moment estimate.
The indicator stability estimate transfers the existing small-set expansion bound
from finite sets to indicator-valued functions. The one-third corollary reuses the
general stable-influence statement; the remaining results are proof obligations.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014;
  May 2021 arXiv edition, Chapter 9, §§9.1–9.5 and Exercise 9.18.
-/

open scoped BigOperators Classical

namespace BooleanAnalysis.Hypercontractivity

/-- An indicator-valued cube function of mean `α` has noise stability at most
`α ^ (2 / (1 + ρ))` for `0 < ρ ≤ 1`.
[OD14, §9.5, Small-Set Expansion Theorem, p. 264]

**Proof sketch.** Take the finite set of cube points where the function equals one.
Its indicator equals the function, and its volume equals the function's mean.
Substitute these identities into the existing small-set expansion theorem. -/
private lemma indicator_stability_le {n : ℕ} (f : BooleanFunc n)
    (hf : ∀ x, f x = 0 ∨ f x = 1) (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) :
    innerProduct f (noiseOp ρ f) ≤
      (expect f) ^ (2 / (1 + ρ)) := (by
  let A : Finset (BoolCube n) := Finset.univ.filter (fun x => f x = 1)
  have hA : SmallSetExpansion.setIndicator A = f := by
    funext x
    rcases hf x with hx | hx <;>
      simp [SmallSetExpansion.setIndicator, cubeIndicator, A, hx]
  simpa only [SmallSetExpansion.volume, hA] using
    SmallSetExpansion.small_set_expansion ρ hρ0 hρ1 A
)

/-- An indicator of positive mean `α` has squared correlation at most
`2 α² log(1/α)` with any unit-variance Rademacher linear form.
[OD14, §9.5 and Ex. 9.18(b)]

**Proof sketch.** The Rademacher exponential-moment bound and the conditional moment
estimate bound the correlation for every real parameter. Choose the parameter to
be the correlation divided by `α`, multiply by `2 α`, and rearrange. -/
private lemma indicator_linear_form_sq_le {n : ℕ} (f : BooleanFunc n)
    (hf : ∀ x, f x = 0 ∨ f x = 1) (hα : 0 < expect f)
    (a : Fin n → ℝ) (hnorm : ∑ i : Fin n, a i ^ 2 = 1) :
    innerProduct f (fun x => ∑ i : Fin n, a i * boolToSign (x i)) ^ 2 ≤
      2 * expect f ^ 2 * Real.log (1 / expect f) :=
  (by
  let L : BooleanFunc n := fun x => ∑ i : Fin n, a i * boolToSign (x i)
  let c : ℝ := innerProduct f L
  have h : (c / expect f) * c ≤
      expect f * ((c / expect f) ^ 2 / 2 - Real.log (expect f)) :=
    indicator_innerProduct_le_of_mgf f L hf hα (c / expect f)
      ((c / expect f) ^ 2 / 2) (ThresholdFunctions.rademacher_mgf_le a hnorm _)
  have hzero : c ^ 2 + 2 * expect f ^ 2 * Real.log (expect f) ≤ 0 := by
    calc
      _ = 2 * expect f * ((c / expect f) * c -
          expect f * ((c / expect f) ^ 2 / 2 - Real.log (expect f))) := by
        field_simp [hα.ne']
        ring
      _ ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr h)
  change c ^ 2 ≤ 2 * expect f ^ 2 * Real.log (1 / expect f)
  rw [one_div, Real.log_inv]
  linarith
)

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
    cubeLpNorm q f ≤ Real.sqrt (q - 1) ^ k * l2Norm f := (by
  let r : ℝ := Real.sqrt (q - 1)
  have hr : 1 ≤ r := Real.one_le_sqrt.mpr (by linarith)
  have hcancel : noiseOp (1 / r) (noiseOp r f) = f := by
    rw [SimpleHypercontractivity.noiseOp_compose,
      one_div_mul_cancel (ne_of_gt (lt_of_lt_of_le zero_lt_one hr))]
    funext x
    simpa only [noiseOp, one_pow, one_mul] using (walsh_expansion f x).symm
  have hc := GeneralHypercontractivity.general_one_function_hypercontractivity
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
          (SimpleHypercontractivity.expect_rpow_abs_nonneg q f) _) (mul_pos ht0 hf).le)
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


/-- For `ρ ≥ 0`, the noisy influence of a coordinate equals the squared second norm
of its derivative after noise at parameter `√ρ`.
[OD14, §2.2 and Cor. 9.25 (proof)]
This Fourier identity holds for arbitrary real-valued functions, without an upper
bound on `ρ`.

**Proof sketch.** Expand the derivative's noise stability in Fourier coefficients.
Its coefficients vanish on sets containing the coordinate; adjoining that coordinate
to every remaining set gives the noisy-influence sum, with the degree reduced by one.
Self-adjointness and composition of noise operators identify this stability with
the squared second norm after noise at `√ρ`. The argument retains the degree-zero
term when `ρ = 0`. -/
private lemma noisyInfluence_eq_sq_norm_derivative {n : ℕ} (f : BooleanFunc n)
    (i : Fin n) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    KKL.noisyInfluence ρ i f =
      l2Norm (noiseOp (Real.sqrt ρ) (derivative i f)) ^ 2 :=
  (by
  classical
  rw [l2Norm, Real.sq_sqrt (innerProduct_self_nonneg _),
    noiseOp_self_adjoint, SimpleHypercontractivity.noiseOp_compose,
    ← pow_two, Real.sq_sqrt hρ, stability_formula, KKL.noisyInfluence]
  have hcoeff :
      (∑ S : Finset (Fin n), ρ ^ S.card * fourierCoeff (derivative i f) S ^ 2) =
        ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => i ∉ S),
          ρ ^ S.card * fourierCoeff f (insert i S) ^ 2 := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro S _
    by_cases h : i ∈ S <;> simp [fourierCoeff_derivative, h]
  rw [hcoeff, ← Finset.sum_filter]
  refine Finset.sum_bij' (fun S _ => S.erase i) (fun S _ => insert i S)
    ?_ ?_ ?_ ?_ ?_
  · intro S hS
    simp
  · intro S hS
    simp
  · intro S hS
    exact Finset.insert_erase (Finset.mem_filter.mp hS).2
  · intro S hS
    exact Finset.erase_insert (Finset.mem_filter.mp hS).2
  · intro S hS
    have hiS := (Finset.mem_filter.mp hS).2
    simp only [Finset.card_erase_of_mem hiS, Finset.insert_erase hiS]
)


/-- Every positive absolute moment of a coordinate derivative of a `±1`-valued
cube function equals that coordinate's ordinary influence.
[OD14, Cor. 9.25 (proof)] The identity is stated for every positive exponent,
since the derivative's absolute value is always zero or one.

**Proof sketch.** The derivative's square equals its absolute value, forcing that
absolute value to be zero or one. Positive powers preserve these values.
Therefore the absolute moment equals the expected derivative square, which is
the ordinary influence. -/
private lemma derivative_abs_moment_eq_influence {n : ℕ} (f : BooleanFunc n)
    (hf : isPmOne f) (i : Fin n) (p : ℝ) (hp : 0 < p) :
    expect (fun x => |derivative i f x| ^ p) = influence i f :=
  (by
  rw [ThresholdFunctions.influence_eq_expect_derivative_sq]
  congr 1
  funext x
  have hs := ThresholdFunctions.derivative_sq_eq_abs_of_pmOne hf i x
  rw [hs]
  have habs : |derivative i f x| * (|derivative i f x| - 1) = 0 := by
    nlinarith [sq_abs (derivative i f x)]
  rcases mul_eq_zero.mp habs with hz | ho
  · rw [hz, Real.zero_rpow hp.ne']
  · have hone : |derivative i f x| = 1 := sub_eq_zero.mp ho
    rw [hone, Real.one_rpow]
)


/-- Stable influence at `ρ ∈ [0,1]` is at most ordinary influence to the power
`2/(1+ρ)` for Boolean functions. [OD14, Cor. 9.25]

**Proof sketch.** Apply `(1+ρ,2)`-hypercontractivity to the coordinate derivative and
evaluate its norm using its `{-1,0,1}`-valued range. -/
theorem stableInfluence_le {n : ℕ} (f : BooleanFunc n) (hf : isPmOne f)
    (i : Fin n) (ρ : ℝ) (hρ : ρ ∈ Set.Icc 0 1) :
    KKL.noisyInfluence ρ i f ≤ (influence i f) ^ (2 / (1 + ρ)) := (by
  rcases hρ with ⟨hρ0, hρ1⟩
  have hp : 0 < 1 + ρ := by linarith
  have hc := GeneralHypercontractivity.general_one_function_hypercontractivity
    (1 + ρ) 2 (by linarith) (by linarith) (by norm_num)
    (Real.sqrt ρ) (Real.sqrt_nonneg _)
    (by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hρ1)
    (by norm_num) (derivative i f)
  rw [derivative_abs_moment_eq_influence f hf i (1 + ρ) hp] at hc
  have hcontract :
      l2Norm (noiseOp (Real.sqrt ρ) (derivative i f)) ≤
        (influence i f) ^ (1 / (1 + ρ)) := by
    simpa only [l2Norm, innerProduct, Real.sqrt_eq_rpow, Real.rpow_two,
      pow_two, abs_mul_abs_self] using hc
  have hI : 0 ≤ influence i f := by
    rw [ThresholdFunctions.influence_eq_expect_derivative_sq]
    exact ThresholdFunctions.expect_nonneg (fun x => sq_nonneg _)
  rw [noisyInfluence_eq_sq_norm_derivative f i ρ hρ0]
  convert pow_le_pow_left₀ (Real.sqrt_nonneg _) hcontract 2 using 1
  rw [← Real.rpow_mul_natCast hI]
  congr 1
  norm_num; ring
)

/-- The one-third-stable influence of a Boolean function is at most its ordinary influence
to the power `3/2`. [OD14, Cor. 9.12]

**Proof sketch.** Specialize the general stable-influence bound to `ρ=1/3` and
simplify the exponent `2/(1+ρ)` to `3/2`. -/
theorem stableInfluence_one_third {n : ℕ} (f : BooleanFunc n) (hf : isPmOne f) (i : Fin n) :
    KKL.noisyInfluence (1 / 3) i f ≤ (influence i f) ^ (3 / 2 : ℝ) := by
  convert stableInfluence_le f hf i (1 / 3) (by norm_num) using 1 <;> norm_num

/-- For `0 ≤ ρ ≤ 1`, multiplying the Fourier weight through level `k` by `ρ ^ k`
gives a lower bound on the noise stability.
[OD14, §9.5, Level-k Inequalities proof]

**Proof sketch.** Expand noise stability as the weighted sum of squared Fourier
coefficients. On levels at most `k`, the weight `ρ ^ |S|` is at least `ρ ^ k`.
Above `k`, the truncated weight is zero and the stability summand is nonnegative.
Multiply by the squared coefficients and sum. -/
private lemma weighted_fourierWeightUpTo_le_stability {n k : ℕ}
    (f : BooleanFunc n) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    ρ ^ k * ThresholdFunctions.fourierWeightUpTo k f ≤
      innerProduct f (noiseOp ρ f) := (by
  rw [ThresholdFunctions.fourierWeightUpTo, stability_formula, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro S _
  by_cases hS : S.card ≤ k
  · simp only [if_pos hS]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_of_le_one hρ0 hρ1 hS) (sq_nonneg _)
  · simp only [if_neg hS, mul_zero]
    positivity
)

/-- For `0 < α ≤ 1` and `ρ ≥ 0`, the power `α ^ (2 / (1 + ρ))` is at most
`α² exp(2 ρ log(1/α))`. [OD14, §9.5, Level-k Inequalities proof]

**Proof sketch.** Since `2 (1 - ρ) ≤ 2 / (1 + ρ)` and `α ≤ 1`, decreasing
the exponent to `2 (1 - ρ)` increases the power. Express that power using
the exponential and logarithm, then separate the square of `α`. -/
private lemma indicator_rpow_le_sq_mul_exp (α ρ : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hρ : 0 ≤ ρ) :
    α ^ (2 / (1 + ρ)) ≤
      α ^ 2 * Real.exp (2 * ρ * Real.log (1 / α)) := (by
  have hden : 0 < 1 + ρ := by positivity
  have hcomp : 2 * (1 - ρ) ≤ 2 / (1 + ρ) :=
    (le_div_iff₀ hden).mpr (by nlinarith [sq_nonneg ρ])
  calc
    α ^ (2 / (1 + ρ)) ≤ α ^ (2 * (1 - ρ)) :=
      Real.rpow_le_rpow_of_exponent_ge hα hα1 hcomp
    _ = α ^ 2 * Real.exp (2 * ρ * Real.log (1 / α)) := by
      rw [Real.rpow_def_of_pos hα, ← Real.rpow_natCast α 2,
        Real.rpow_def_of_pos hα, one_div, Real.log_inv, ← Real.exp_add]
      congr 1
      ring
)

/-- If `0 < α ≤ 1`, `1 ≤ k ≤ 2 log(1/α)`, and
`ρ ^ k W ≤ α ^ (2 / (1 + ρ))` for every `0 < ρ ≤ 1`, then
`W ≤ ((2e/k) log(1/α)) ^ k α²`.
[OD14, §9.5, Level-k Inequalities proof]

**Proof sketch.** Write `L = log(1/α)` and choose `ρ = k / (2L)`, which
lies in `(0, 1]`. The scalar exponent bound gives `ρ ^ k W ≤ α² exp(k)`.
The product of `ρ ^ k` and `((2e/k)L) ^ k` equals `exp(k)`.
Cancel the positive factor `ρ ^ k`. -/
private lemma level_k_optimization {k : ℕ} (α W : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hk : 0 < k)
    (hkα : (k : ℝ) ≤ 2 * Real.log (1 / α))
    (hW : ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ρ ^ k * W ≤ α ^ (2 / (1 + ρ))) :
    W ≤ ((2 * Real.exp 1 / (k : ℝ)) * Real.log (1 / α)) ^ k * α ^ 2 :=
  (by
  let L : ℝ := Real.log (1 / α)
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have hL : 0 < L := by
    dsimp [L]
    linarith
  let ρ : ℝ := (k : ℝ) / (2 * L)
  have hρ0 : 0 < ρ := div_pos hkR (by positivity)
  have hρ1 : ρ ≤ 1 := (div_le_one (by positivity)).mpr hkα
  have hexp : 2 * ρ * L = (k : ℝ) := by
    calc
      _ = ρ * (2 * L) := by ring
      _ = (k : ℝ) := div_mul_cancel₀ _ (by positivity)
  have hbound : ρ ^ k * W ≤ α ^ 2 * Real.exp (k : ℝ) := by
    calc
      _ ≤ α ^ (2 / (1 + ρ)) := hW ρ hρ0 hρ1
      _ ≤ α ^ 2 * Real.exp (2 * ρ * L) :=
        indicator_rpow_le_sq_mul_exp α ρ hα hα1 hρ0.le
      _ = _ := by rw [hexp]
  have hprod : ρ * ((2 * Real.exp 1 / (k : ℝ)) * L) = Real.exp 1 := by
    dsimp [ρ]
    field_simp [hL.ne', hkR.ne']
  apply le_of_mul_le_mul_left ?_ (pow_pos hρ0 k)
  calc
    ρ ^ k * W ≤ α ^ 2 * Real.exp (k : ℝ) := hbound
    _ = ρ ^ k * (((2 * Real.exp 1 / (k : ℝ)) * L) ^ k * α ^ 2) := by
      rw [← mul_assoc, ← mul_pow, hprod, ← Real.exp_nat_mul, mul_one]
      ring
)

/-- For an indicator of positive mean `α` and `1 ≤ k ≤ 2 ln(1/α)`, its Fourier weight
through level `k` is at most `((2e/k) ln(1/α))^k α²`.
[OD14, §9.5, Level-k Inequalities] The zero indicator is excluded from the logarithmic formula.

**Proof sketch.** Small-set expansion bounds the weight by `ρ^(-k) α^(2/(1+ρ))`.
Weaken the exponent to `2(1-ρ)` and set `ρ = k/(2 ln(1/α))`. -/
theorem level_k_inequality {n k : ℕ} (f : BooleanFunc n)
    (hf : ∀ x, f x = 0 ∨ f x = 1) (hα : 0 < expect f) (hk : 0 < k)
    (hkα : (k : ℝ) ≤ 2 * Real.log (1 / expect f)) :
    ThresholdFunctions.fourierWeightUpTo k f ≤
      ((2 * Real.exp 1 / (k : ℝ)) * Real.log (1 / expect f)) ^ k * (expect f) ^ 2 := (by
  have hα1 : expect f ≤ 1 := by
    calc
      _ ≤ expect (fun _ : BoolCube n => (1 : ℝ)) :=
        ThresholdFunctions.expect_mono fun x => by
          rcases hf x with hx | hx <;> simp [hx]
      _ = 1 := ThresholdFunctions.expect_const 1
  apply level_k_optimization (expect f)
    (ThresholdFunctions.fourierWeightUpTo k f) hα hα1 hk hkα
  intro ρ hρ0 hρ1
  exact (weighted_fourierWeightUpTo_le_stability f ρ hρ0.le hρ1).trans
    (indicator_stability_le f hf ρ hρ0 hρ1)
)


/-- An indicator of positive mean `α` has level-one Fourier weight at most
`2α² ln(1/α)`. [OD14, §9.5 and Ex. 9.18(b)]

**Proof sketch.** Use the subgaussian exponential moment bound for the normalized
degree-one part, and optimize its exponential parameter on the indicator's support. -/
theorem level_one_inequality {n : ℕ} (f : BooleanFunc n)
    (hf : ∀ x, f x = 0 ∨ f x = 1) (hα : 0 < expect f) :
    weightLevel 1 f ≤ 2 * (expect f) ^ 2 * Real.log (1 / expect f) := (by
  have hα1 : expect f ≤ 1 := by
    calc
      _ ≤ expect (fun _ : BoolCube n => (1 : ℝ)) :=
        ThresholdFunctions.expect_mono fun x => by
          rcases hf x with hx | hx <;> simp [hx]
      _ = 1 := ThresholdFunctions.expect_const 1
  have hlog : 0 ≤ Real.log (1 / expect f) :=
    Real.log_nonneg ((one_le_div hα).mpr hα1)
  rcases (ThresholdFunctions.weightLevel_nonneg 1 f).eq_or_lt with hw0 | hw
  · rw [← hw0]
    positivity
  obtain ⟨a, hnorm, hcorr⟩ := ThresholdFunctions.exists_unit_linear_form f hw
  have h := indicator_linear_form_sq_le f hf hα a hnorm
  simpa only [innerProduct, hcorr, Real.sq_sqrt hw.le] using h
)


end BooleanAnalysis.Hypercontractivity
