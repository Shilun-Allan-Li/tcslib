/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Exp

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Error reduction by repetition: the Chernoff core

The probabilistic heart of Arora–Barak's error-reduction theorem
([AB09, Thm 7.10]): run `k` independent trials of a decision procedure that
is correct with probability `p ≥ 1/2 + ε` and take the majority; the
probability that the majority is wrong is exponentially small in `k`.

This file states the machine-independent core over i.i.d. Bernoulli random
variables: the Chernoff-type concentration bound [AB09, Cor 7.11] and the
majority-vote error bound instantiating [AB09, Thm 7.10]'s calculation.
Wrapping these into statements about `BPP`-style verifier classes is Tier B
work and lives elsewhere.

## Main results

* `Randomized.iid_bernoulli_avg_concentration` — [AB09, Cor 7.11], with a
  corrected constant (see **Deviations**).
* `Randomized.majority_error_le` — the calculation proving [AB09, Thm 7.10].
* `Randomized.iidBernoulli_tail_le` — the shared one-sided Hoeffding bound,
  from Mathlib's sub-Gaussian machinery
  (`ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun`).

## Deviations from the source

* [AB09, Cor 7.11] is stated for abstract i.i.d. Boolean random variables
  `X₁,…,X_k` with `Pr[Xᵢ = 1] = p`; we realize them concretely as the product
  measure of `k` Bernoulli(`p`) distributions on `Fin k → Bool`, which is the
  same joint distribution.
* **Erratum.** [AB09, Cor 7.11] prints the bound
  `Pr[|(1/k)ΣXᵢ − p| > δ] < e^{−(δ²/4)pk}`, which is false: for a single
  trial (`k = 1`) with `p = 1/2` and `δ = 1/4`, the deviation event has
  probability `1` while the claimed bound is `e^{−1/128} < 1`.  We state the
  standard two-sided Hoeffding bound `≤ 2·e^{−2δ²k}` instead, which is what
  the error-reduction argument needs.
* [AB09, Thm 7.10] is stated for polynomial-time PTMs, with
  `p = 1/2 + |x|^{−c}` and final bound `2^{−|x|^d}`; `majority_error_le` is
  its probabilistic content with `ε` in place of `|x|^{−c}`: the one-sided
  Hoeffding bound gives majority error at most `e^{−2ε²k}`, which for
  `k = Θ((n+1)^{2c+d})` is at most `2^{−(n+1)^d}`.  The book's displayed
  intermediate step normalizes the sum by `1/n` where `1/k` is meant; we
  state it with `1/k`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Randomized

open MeasureTheory
open scoped NNReal ENNReal

/-- The joint distribution of `k` independent Bernoulli(`p`) trials, as a
measure on `Fin k → Bool`.  [AB09, Cor 7.11: "independent identically
distributed Boolean random variables"] -/
noncomputable def iidBernoulli (k : ℕ) (p : ℝ≥0) (hp : p ≤ 1) :
    Measure (Fin k → Bool) :=
  Measure.pi fun _ => (PMF.bernoulli p hp).toMeasure

/-- The number of successes among the `k` trials `ω`, as a real number. -/
def successCount {k : ℕ} (ω : Fin k → Bool) : ℝ :=
  ∑ i, if ω i then (1 : ℝ) else 0

instance isProbabilityMeasure_iidBernoulli (k : ℕ) (p : ℝ≥0) (hp : p ≤ 1) :
    IsProbabilityMeasure (iidBernoulli k p hp) := by
  unfold iidBernoulli
  infer_instance

/-- The indicator of success in the `i`-th trial, as a real random variable. -/
def coordIndicator (k : ℕ) (i : Fin k) (ω : Fin k → Bool) : ℝ :=
  if ω i then 1 else 0

/-- The coordinate indicator is measurable: a discrete function of one coordinate. -/
theorem measurable_coordIndicator {k : ℕ} (i : Fin k) :
    Measurable (coordIndicator k i) := by
  unfold coordIndicator
  exact (Measurable.of_discrete (f := fun b : Bool => if b then (1 : ℝ) else 0)).comp
    (measurable_pi_apply i)

/-- Under the i.i.d. Bernoulli measure, each trial succeeds with
probability `p` in expectation. -/
theorem integral_coordIndicator {p : ℝ≥0} (hp : p ≤ 1) {k : ℕ} (i : Fin k) :
    ∫ ω, coordIndicator k i ω ∂(iidBernoulli k p hp) = (p : ℝ) := by
  have hmp : MeasurePreserving (Function.eval i) (iidBernoulli k p hp)
      ((PMF.bernoulli p hp).toMeasure) :=
    measurePreserving_eval
      (μ := fun _ : Fin k => (PMF.bernoulli p hp).toMeasure) i
  have hmap := integral_map (φ := Function.eval i) (μ := iidBernoulli k p hp)
    (f := fun b : Bool => if b then (1 : ℝ) else 0)
    (measurable_pi_apply i).aemeasurable
    Measurable.of_discrete.aestronglyMeasurable
  calc ∫ ω, coordIndicator k i ω ∂(iidBernoulli k p hp)
      = ∫ b, (if b then (1 : ℝ) else 0)
          ∂(Measure.map (Function.eval i) (iidBernoulli k p hp)) := hmap.symm
    _ = ∫ b, (if b then (1 : ℝ) else 0) ∂((PMF.bernoulli p hp).toMeasure) := by
        rw [hmp.map_eq]
    _ = (p : ℝ) := by
        simp only [← Bool.cond_eq_ite]
        exact PMF.bernoulli_expectation hp

/-- The coordinate indicator takes values in `[0,1]`, hence is integrable under the
`k`-fold Bernoulli measure. -/
theorem integrable_coordIndicator {p : ℝ≥0} (hp : p ≤ 1) {k : ℕ} (i : Fin k) :
    Integrable (coordIndicator k i) (iidBernoulli k p hp) :=
  Integrable.of_mem_Icc 0 1 (measurable_coordIndicator i).aemeasurable
    (MeasureTheory.ae_of_all _ fun ω => by
      unfold coordIndicator
      split <;> norm_num)

/-- The trial indicators are independent under the product measure. -/
theorem iIndepFun_coordIndicator {p : ℝ≥0} (hp : p ≤ 1) (k : ℕ) :
    ProbabilityTheory.iIndepFun (coordIndicator k) (iidBernoulli k p hp) :=
  ProbabilityTheory.iIndepFun_pi
    (X := fun _ : Fin k => fun b : Bool => if b then (1 : ℝ) else 0)
    (μ := fun _ : Fin k => (PMF.bernoulli p hp).toMeasure)
    fun _ => Measurable.of_discrete.aemeasurable

/-- Hoeffding's lemma for a centered trial: `Xᵢ − p` is sub-Gaussian with
parameter `(1/2)² = 1/4`. -/
theorem hasSubgaussianMGF_coordIndicator_sub {p : ℝ≥0} (hp : p ≤ 1) {k : ℕ}
    (i : Fin k) :
    ProbabilityTheory.HasSubgaussianMGF
      (fun ω => coordIndicator k i ω - (p : ℝ)) ((1 / 2 : ℝ≥0) ^ 2)
      (iidBernoulli k p hp) := by
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := p.coe_nonneg
  have hp1 : (p : ℝ) ≤ 1 := hp
  have h := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    (μ := iidBernoulli k p hp)
    (X := fun ω => coordIndicator k i ω - (p : ℝ))
    (a := -(p : ℝ)) (b := 1 - (p : ℝ))
    ((measurable_coordIndicator i).sub_const _).aemeasurable
    (MeasureTheory.ae_of_all _ fun ω => by
      have hbeta : (fun ω : Fin k → Bool => coordIndicator k i ω - (p : ℝ)) ω
          = (if ω i then (1 : ℝ) else 0) - p := rfl
      rw [hbeta, Set.mem_Icc]
      by_cases h : ω i
      · rw [if_pos h]
        constructor <;> linarith
      · rw [if_neg h]
        constructor <;> linarith)
    (by
      rw [integral_sub (integrable_coordIndicator hp i) (integrable_const _),
        integral_coordIndicator hp, integral_const]
      simp)
  have h2 : ((‖(1 - (p : ℝ)) - -(p : ℝ)‖₊ / 2 : ℝ≥0) ^ 2) = (1 / 2 : ℝ≥0) ^ 2 := by
    rw [show (1 - (p : ℝ)) - -(p : ℝ) = 1 from by ring, nnnorm_one]
  rw [← h2]
  exact h

/-- Hoeffding's lemma for the reflected centered trial: `p − Xᵢ` is
sub-Gaussian with parameter `(1/2)² = 1/4`. -/
theorem hasSubgaussianMGF_sub_coordIndicator {p : ℝ≥0} (hp : p ≤ 1) {k : ℕ}
    (i : Fin k) :
    ProbabilityTheory.HasSubgaussianMGF
      (fun ω => (p : ℝ) - coordIndicator k i ω) ((1 / 2 : ℝ≥0) ^ 2)
      (iidBernoulli k p hp) :=
  (hasSubgaussianMGF_coordIndicator_sub hp i).neg.congr
    (MeasureTheory.ae_of_all _ fun ω => by
      show -(coordIndicator k i ω - (p : ℝ)) = _
      ring)

/-- **One-sided Hoeffding bound for the trials**: for any family `Y` of
independent `(1/4)`-sub-Gaussian functions of the trials (in practice the
centered indicators `±(Xᵢ − p)`),
`Pr[Σᵢ Yᵢ ≥ tk] ≤ e^{−2t²k}`. -/
theorem iidBernoulli_tail_le {p : ℝ≥0} (hp : p ≤ 1) {k : ℕ} (hk : 0 < k)
    {Y : Fin k → (Fin k → Bool) → ℝ}
    (hYind : ProbabilityTheory.iIndepFun Y (iidBernoulli k p hp))
    (hsubG : ∀ i, ProbabilityTheory.HasSubgaussianMGF (Y i) ((1 / 2 : ℝ≥0) ^ 2)
      (iidBernoulli k p hp))
    {t : ℝ} (ht : 0 ≤ t) :
    iidBernoulli k p hp {ω | t * k ≤ ∑ i, Y i ω} ≤
      ENNReal.ofReal (Real.exp (-2 * t ^ 2 * k)) := by
  have hH := ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hYind
    (c := fun _ : Fin k => (1 / 2 : ℝ≥0) ^ 2) (s := Finset.univ)
    (fun i _ => hsubG i) (ε := t * k)
    (mul_nonneg ht (Nat.cast_nonneg k))
  rw [ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (Real.exp_nonneg _),
    ← measureReal_def]
  refine hH.trans (le_of_eq ?_)
  congr 1
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have hsum : ((∑ _i : Fin k, ((1 / 2 : ℝ≥0) ^ 2) : ℝ≥0) : ℝ) = k / 4 := by
    push_cast
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  push_cast [hsum]
  field_simp
  ring

/-- **Concentration for i.i.d. Boolean trials** (the role of
[AB09, Cor 7.11], stated as the two-sided Hoeffding bound).  Let `X₁,…,X_k`
be i.i.d. Boolean random variables with `Pr[Xᵢ = 1] = p`, and `δ > 0`.  Then
`Pr[|(1/k)Σᵢ Xᵢ − p| > δ] ≤ 2·e^{−2δ²k}`.

The book's printed bound `< e^{−(δ²/4)pk}` is false (see the module
docstring's **Erratum**); this is the standard replacement, and suffices for
[AB09, Thm 7.10].

**Proof sketch.** Hoeffding's inequality for sums of independent bounded
random variables (in Mathlib: `measure_sum_ge_le_of_iIndepFun` for
sub-Gaussian summands; a `{0,1}`-valued variable is sub-Gaussian with
parameter `1/4` by Hoeffding's lemma), applied to `Xᵢ − p` on each of the
two tails with threshold `t = δk`, each tail contributing `e^{−2δ²k}`. -/
theorem iid_bernoulli_avg_concentration {p : ℝ≥0} (hp : p ≤ 1) {k : ℕ}
    (hk : 0 < k) {δ : ℝ} (hδ0 : 0 < δ) :
    iidBernoulli k p hp {ω | δ < |successCount ω / k - (p : ℝ)|} ≤
      ENNReal.ofReal (2 * Real.exp (-2 * δ ^ 2 * k)) := by
  classical
  have hk0 : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  -- Split the two-sided deviation into the two one-sided tails.
  have hsub : {ω : Fin k → Bool | δ < |successCount ω / k - (p : ℝ)|} ⊆
      {ω | δ * k ≤ ∑ i, (coordIndicator k i ω - (p : ℝ))} ∪
      {ω | δ * k ≤ ∑ i, ((p : ℝ) - coordIndicator k i ω)} := fun ω hω => by
    rw [Set.mem_setOf_eq, lt_abs] at hω
    have hsum1 : ∑ i, (coordIndicator k i ω - (p : ℝ))
        = successCount ω - k * p := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_comm]
      rfl
    have hsum2 : ∑ i, ((p : ℝ) - coordIndicator k i ω)
        = k * p - successCount ω := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      rfl
    rcases hω with h | h
    · left
      rw [Set.mem_setOf_eq, hsum1]
      have h2 : (δ + (p : ℝ)) * k < successCount ω := by
        rw [← lt_div_iff₀ hk0]
        linarith
      nlinarith
    · right
      rw [Set.mem_setOf_eq, hsum2]
      have h2 : successCount ω < ((p : ℝ) - δ) * k := by
        rw [← div_lt_iff₀ hk0]
        linarith
      nlinarith
  -- Independence of the two centered families.
  have hXind := iIndepFun_coordIndicator hp k
  have hind1 : ProbabilityTheory.iIndepFun
      (fun i ω => coordIndicator k i ω - (p : ℝ)) (iidBernoulli k p hp) :=
    hXind.comp (fun _ : Fin k => fun x : ℝ => x - (p : ℝ))
      fun _ => measurable_id.sub_const _
  have hind2 : ProbabilityTheory.iIndepFun
      (fun i ω => (p : ℝ) - coordIndicator k i ω) (iidBernoulli k p hp) :=
    hXind.comp (fun _ : Fin k => fun x : ℝ => (p : ℝ) - x)
      fun _ => measurable_id.const_sub _
  have h1 := iidBernoulli_tail_le hp hk hind1
    (fun i => hasSubgaussianMGF_coordIndicator_sub hp i) hδ0.le
  have h2 := iidBernoulli_tail_le hp hk hind2
    (fun i => hasSubgaussianMGF_sub_coordIndicator hp i) hδ0.le
  calc iidBernoulli k p hp {ω | δ < |successCount ω / k - (p : ℝ)|}
      ≤ iidBernoulli k p hp
          ({ω | δ * k ≤ ∑ i, (coordIndicator k i ω - (p : ℝ))} ∪
            {ω | δ * k ≤ ∑ i, ((p : ℝ) - coordIndicator k i ω)}) :=
        measure_mono hsub
    _ ≤ iidBernoulli k p hp
          {ω | δ * k ≤ ∑ i, (coordIndicator k i ω - (p : ℝ))} +
        iidBernoulli k p hp
          {ω | δ * k ≤ ∑ i, ((p : ℝ) - coordIndicator k i ω)} :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-2 * δ ^ 2 * k)) +
          ENNReal.ofReal (Real.exp (-2 * δ ^ 2 * k)) := add_le_add h1 h2
    _ = ENNReal.ofReal (2 * Real.exp (-2 * δ ^ 2 * k)) := by
        rw [← ENNReal.ofReal_add (Real.exp_nonneg _) (Real.exp_nonneg _)]
        congr 1
        ring

/-- **Majority-vote error reduction, concentration core** (the calculation
proving [AB09, Thm 7.10]).  If each of `k` i.i.d. trials succeeds with
probability `p ≥ 1/2 + ε`, the probability that at most half the trials
succeed — i.e. that the majority vote errs — is at most `e^{−2ε²k}`
(one-sided Hoeffding; the book's `e^{−(δ²/4)pk}`-based route is unsound,
see the module docstring's **Erratum**).

For advantage `ε ≥ (n+1)^{−c}/6` and `k = Θ((n+1)^{2c+d})` repetitions this
is at most `2^{−(n+1)^d}`, which is [AB09, Thm 7.10]'s bound.

**Proof sketch.** If at most half the trials succeed then
`(1/k)Σᵢ Xᵢ ≤ 1/2 ≤ p − ε`, so the lower tail `Σᵢ(Xᵢ − p) ≤ −εk` has
occurred; one-sided Hoeffding for independent `{0,1}`-valued summands bounds
it by `e^{−2ε²k}`. -/
theorem majority_error_le {p : ℝ≥0} (hp : p ≤ 1) {ε : ℝ} (hε : 0 < ε)
    (hpε : 1 / 2 + ε ≤ (p : ℝ)) {k : ℕ} (hk : 0 < k) :
    iidBernoulli k p hp {ω | 2 * successCount ω ≤ k} ≤
      ENNReal.ofReal (Real.exp (-2 * ε ^ 2 * k)) := by
  classical
  have hk0 : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hsub : {ω : Fin k → Bool | 2 * successCount ω ≤ k} ⊆
      {ω | ε * k ≤ ∑ i, ((p : ℝ) - coordIndicator k i ω)} := fun ω hω => by
    have hsum : ∑ i, ((p : ℝ) - coordIndicator k i ω)
        = k * p - successCount ω := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      rfl
    rw [Set.mem_setOf_eq] at hω
    rw [Set.mem_setOf_eq, hsum]
    have h3 : (k : ℝ) * (1 / 2 + ε) ≤ k * p :=
      mul_le_mul_of_nonneg_left hpε hk0.le
    nlinarith
  have hind : ProbabilityTheory.iIndepFun
      (fun i ω => (p : ℝ) - coordIndicator k i ω) (iidBernoulli k p hp) :=
    (iIndepFun_coordIndicator hp k).comp
      (fun _ : Fin k => fun x : ℝ => (p : ℝ) - x)
      fun _ => measurable_id.const_sub _
  exact (measure_mono hsub).trans (iidBernoulli_tail_le hp hk hind
    (fun i => hasSubgaussianMGF_sub_coordIndicator hp i) hε.le)

end Randomized
