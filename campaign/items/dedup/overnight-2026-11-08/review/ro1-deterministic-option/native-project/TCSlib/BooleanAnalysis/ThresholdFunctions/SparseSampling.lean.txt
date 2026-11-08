import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Independence.Basic
import TCSlib.BooleanAnalysis.ThresholdFunctions.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Sampling sparse Fourier representations

This file constructs a single sample of Fourier characters whose signed average uniformly
approximates a nonzero Boolean function. The construction uses a finite probability mass function,
Hoeffding's inequality, and a union bound over the Boolean cube.

## Main definitions

No new definitions are exported.

## Main results

* `spectralOneNorm_pos`: a nonzero function has positive spectral one-norm.
* `sparse_signed_sample`: a uniformly accurate average of sampled signed Walsh characters.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014;
  arXiv edition, 2021, Theorem 5.12.
* [BS92] J. Bruck and R. Smolensky, Polynomial threshold functions and sparse polynomials, 1992.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace BooleanAnalysis.ThresholdFunctions

/-- A one-sided Hoeffding estimate for independent variables valued in `[-1,1]`. -/
private theorem sample_tail
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {s : ℕ} {Y : Fin s → Ω → ℝ} {m ε : ℝ}
    (hindep : iIndepFun Y μ)
    (hmeas : ∀ i, AEMeasurable (Y i) μ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, Y i ω ∈ Set.Icc (-1 : ℝ) 1)
    (hmean : ∀ i, ∫ ω, Y i ω ∂μ = m)
    (hs : 0 < s) (hε : 0 ≤ ε) :
    μ.real {ω | (s : ℝ) * ε ≤ ∑ i : Fin s, Y i ω - (s : ℝ) * m} ≤
      Real.exp (-(s : ℝ) * ε ^ 2 / 2) := by
  let X : Fin s → Ω → ℝ := fun i ω ↦ Y i ω - ∫ u, Y i u ∂μ
  have hindepX : iIndepFun X μ :=
    hindep.comp (fun i (y : ℝ) ↦ y - ∫ u, Y i u ∂μ)
      (fun i ↦ measurable_id.sub measurable_const)
  have hsubG : ∀ i : Fin s, HasSubgaussianMGF (X i) 1 μ := by
    intro i
    convert hasSubgaussianMGF_of_mem_Icc (a := (-1 : ℝ)) (b := 1)
      (hmeas i) (hbound i) using 2
    norm_num
  have htail := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
    (ι := Fin s) hindepX (s := Finset.univ) (c := fun _ ↦ (1 : NNReal))
    (fun i _ ↦ hsubG i) (ε := (s : ℝ) * ε)
    (mul_nonneg (Nat.cast_nonneg _) hε)
  have hsum (ω : Ω) : ∑ i : Fin s, X i ω =
      ∑ i : Fin s, Y i ω - (s : ℝ) * m := by
    simp [X, Finset.sum_sub_distrib, hmean]
  calc
    μ.real {ω | (s : ℝ) * ε ≤ ∑ i : Fin s, Y i ω - (s : ℝ) * m} =
      μ.real {ω | (s : ℝ) * ε ≤ ∑ i ∈ Finset.univ, X i ω} := by
        congr 1
        ext ω
        simp [hsum]
    _ ≤ _ := htail
    _ = Real.exp (-(s : ℝ) * ε ^ 2 / 2) := by
      congr 1
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      have hs0 : (s : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      push_cast
      field_simp
      ring


/-- The two-sided Hoeffding estimate, obtained by applying the one-sided bound to `Y` and `-Y`. -/
private theorem sample_abs_tail
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {s : ℕ} {Y : Fin s → Ω → ℝ} {m ε : ℝ}
    (hindep : iIndepFun Y μ)
    (hmeas : ∀ i, AEMeasurable (Y i) μ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, Y i ω ∈ Set.Icc (-1 : ℝ) 1)
    (hmean : ∀ i, ∫ ω, Y i ω ∂μ = m)
    (hs : 0 < s) (hε : 0 ≤ ε) :
    μ.real {ω | (s : ℝ) * ε ≤ |∑ i : Fin s, Y i ω - (s : ℝ) * m|} ≤
      2 * Real.exp (-(s : ℝ) * ε ^ 2 / 2) := by
  let N : Fin s → Ω → ℝ := fun i ω ↦ -Y i ω
  have hindepN : iIndepFun N μ :=
    hindep.comp (fun _ (y : ℝ) ↦ -y) (fun _ ↦ measurable_neg)
  have hmeasN : ∀ i, AEMeasurable (N i) μ := fun i ↦ (hmeas i).neg
  have hboundN : ∀ i, ∀ᵐ ω ∂μ, N i ω ∈ Set.Icc (-1 : ℝ) 1 := by
    intro i
    filter_upwards [hbound i] with ω hω
    dsimp [N]
    constructor <;> linarith [hω.1, hω.2]
  have hmeanN : ∀ i, ∫ ω, N i ω ∂μ = -m := by
    intro i
    change ∫ ω, -Y i ω ∂μ = -m
    rw [integral_neg, hmean i]
  have hU := sample_tail hindep hmeas hbound hmean hs hε
  have hN := sample_tail hindepN hmeasN hboundN hmeanN hs hε
  let U : Set Ω := {ω | (s : ℝ) * ε ≤ ∑ i : Fin s, Y i ω - (s : ℝ) * m}
  let D : Set Ω := {ω | (s : ℝ) * ε ≤ ∑ i : Fin s, N i ω - (s : ℝ) * (-m)}
  have hsub : {ω | (s : ℝ) * ε ≤ |∑ i : Fin s, Y i ω - (s : ℝ) * m|} ⊆ U ∪ D := by
    intro ω hω
    change (s : ℝ) * ε ≤ |∑ i : Fin s, Y i ω - (s : ℝ) * m| at hω
    rcases le_abs.mp hω with h | h
    · exact Or.inl h
    · right
      change (s : ℝ) * ε ≤ ∑ i : Fin s, N i ω - (s : ℝ) * (-m)
      have hsumN : (∑ i : Fin s, N i ω) = -(∑ i : Fin s, Y i ω) := by
        simp [N]
      rw [hsumN]
      linarith
  calc
    μ.real {ω | (s : ℝ) * ε ≤ |∑ i : Fin s, Y i ω - (s : ℝ) * m|} ≤
      μ.real (U ∪ D) := measureReal_mono hsub
    _ ≤ μ.real U + μ.real D := measureReal_union_le U D
    _ ≤ _ := by
      have hD : μ.real D ≤ Real.exp (-(s : ℝ) * ε ^ 2 / 2) := hN
      nlinarith

/-- For positive arity, the union-bound constant is strictly below one. -/
private theorem sparse_numeric (n : ℕ) (hn : 0 < n) :
    (2 : ℝ) ^ (n + 1) * Real.exp (-2 * (n : ℝ)) < 1 := by
  have he : (2 : ℝ) < Real.exp 1 := by
    linarith [Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)]
  have he2 : (4 : ℝ) < Real.exp 2 := by
    have hsq : (2 : ℝ) ^ 2 < (Real.exp 1) ^ 2 := by gcongr
    rw [← Real.exp_nat_mul] at hsq
    norm_num at hsq ⊢
    exact hsq
  have hpow : (4 : ℝ) ^ n < (Real.exp 2) ^ n := by
    gcongr
  have hcomp : (2 : ℝ) ^ (n + 1) ≤ 4 ^ n := by
    have h : n + 1 ≤ 2 * n := by omega
    calc
      (2 : ℝ) ^ (n + 1) ≤ (2 : ℝ) ^ (2 * n) :=
        pow_le_pow_right₀ (by norm_num) h
      _ = 4 ^ n := by rw [pow_mul]; norm_num
  have hcore : (2 : ℝ) ^ (n + 1) < Real.exp (2 * (n : ℝ)) := by
    calc
      _ ≤ 4 ^ n := hcomp
      _ < (Real.exp 2) ^ n := hpow
      _ = Real.exp (2 * (n : ℝ)) := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hneg : -2 * (n : ℝ) = -(2 * (n : ℝ)) := by ring
  rw [hneg, Real.exp_neg, ← div_eq_mul_inv]
  have hepos : 0 < Real.exp (2 * (n : ℝ)) := Real.exp_pos _
  exact (div_lt_iff₀ hepos).mpr (by simpa using hcore)

/-- Translate the sample-size assumption into Hoeffding's exponent. -/
private theorem sparse_param (n s : ℕ) (L δ : ℝ) (hL : 0 < L) (hδ : 0 < δ)
    (hs : 4 * n * L ^ 2 / δ ^ 2 ≤ s) :
    2 * (n : ℝ) ≤ (s : ℝ) * (δ / L) ^ 2 / 2 := by
  have hsqδ : 0 < δ ^ 2 := sq_pos_of_pos hδ
  have hsqL : 0 < L ^ 2 := sq_pos_of_pos hL
  have hhs : 4 * (n : ℝ) * L ^ 2 ≤ (s : ℝ) * δ ^ 2 := by
    exact (div_le_iff₀ hsqδ).mp (by exact_mod_cast hs)
  calc
    2 * (n : ℝ) ≤ ((s : ℝ) * δ ^ 2 / L ^ 2) / 2 := by
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
      apply (le_div_iff₀ hsqL).mpr
      nlinarith
    _ = (s : ℝ) * (δ / L) ^ 2 / 2 := by
      field_simp

/-- The sum of the per-point error bounds over the Boolean cube is below one. -/
private theorem sparse_union_numeric (n s : ℕ) (hn : 0 < n)
    (L δ : ℝ) (hL : 0 < L) (hδ : 0 < δ)
    (hs : 4 * n * L ^ 2 / δ ^ 2 ≤ s) :
    (2 : ℝ) ^ n * (2 * Real.exp (-(s : ℝ) * (δ / L) ^ 2 / 2)) < 1 := by
  have hparam := sparse_param n s L δ hL hδ hs
  have hexp : Real.exp (-(s : ℝ) * (δ / L) ^ 2 / 2) ≤
      Real.exp (-2 * (n : ℝ)) := by
    apply Real.exp_le_exp.mpr
    linarith
  calc
    (2 : ℝ) ^ n * (2 * Real.exp (-(s : ℝ) * (δ / L) ^ 2 / 2)) =
      (2 : ℝ) ^ (n + 1) * Real.exp (-(s : ℝ) * (δ / L) ^ 2 / 2) := by
        rw [pow_succ]
        ring
    _ ≤ (2 : ℝ) ^ (n + 1) * Real.exp (-2 * (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    _ < 1 := sparse_numeric n hn

/-- A finite union of bad events of total measure below one misses a sample. -/
private theorem exists_good_of_union_bound
    {Ω β : Type*} [MeasurableSpace Ω] [Fintype β]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (bad : β → Set Ω) {B : ℝ}
    (hbad : ∀ b, μ.real (bad b) ≤ B)
    (hB : (Fintype.card β : ℝ) * B < 1) :
    ∃ ω : Ω, ∀ b, ω ∉ bad b := by
  have hU : μ.real (⋃ b, bad b) ≤
      ∑ b : β, μ.real (bad b) := measureReal_iUnion_fintype_le bad
  have hsum : (∑ b : β, μ.real (bad b)) ≤ (Fintype.card β : ℝ) * B := by
    calc
      _ ≤ ∑ _ : β, B := Finset.sum_le_sum (fun b _ ↦ hbad b)
      _ = _ := by simp
  have hlt : μ.real (⋃ b, bad b) < 1 := lt_of_le_of_lt (hU.trans hsum) hB
  by_contra h
  push_neg at h
  have hcover : (⋃ b, bad b) = Set.univ := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact h ω
  rw [hcover, measureReal_univ_eq_one] at hlt
  exact (lt_irrefl 1) hlt

section PMFMean

variable (n : ℕ)
local instance : MeasurableSpace (Finset (Fin n)) := ⊤

/-- The spectral probability distribution makes a signed character's mean equal to `f/L`. -/
private theorem sparse_sample_pmf_mean (f : BooleanFunc n)
    (hL : 0 < spectralOneNorm f) :
    ∃ pmf : PMF (Finset (Fin n)),
      ∀ x : BoolCube n,
        ∫ S, thresholdSign (fourierCoeff f S) * chiS S x ∂pmf.toMeasure =
          f x / spectralOneNorm f := by
  classical
  have hsum_real : ∑ S : Finset (Fin n),
      |fourierCoeff f S| / spectralOneNorm f = 1 := by
    rw [← Finset.sum_div, ← spectralOneNorm]
    exact div_self (ne_of_gt hL)
  have hsum : ∑ S : Finset (Fin n),
      ENNReal.ofReal (|fourierCoeff f S| / spectralOneNorm f) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg]
    · rw [hsum_real]
      norm_num
    · intro S _
      positivity
  let pmf : PMF (Finset (Fin n)) :=
    PMF.ofFintype (fun S ↦ ENNReal.ofReal (|fourierCoeff f S| / spectralOneNorm f)) hsum
  have hp (S : Finset (Fin n)) :
      (pmf S).toReal = |fourierCoeff f S| / spectralOneNorm f := by
    simp [pmf, ENNReal.toReal_ofReal (div_nonneg (abs_nonneg _) hL.le)]
  refine ⟨pmf, ?_⟩
  intro x
  have hint :
      ∫ S, thresholdSign (fourierCoeff f S) * chiS S x ∂pmf.toMeasure =
        ∑ S : Finset (Fin n),
          (pmf S).toReal * (thresholdSign (fourierCoeff f S) * chiS S x) := by
    rw [integral_fintype _ .of_finite]
    congr with S
    rw [measureReal_def]
    congr 2
    exact PMF.toMeasure_apply_singleton pmf S (MeasurableSet.singleton _)
  rw [hint]
  have hterm (S : Finset (Fin n)) :
      (pmf S).toReal * (thresholdSign (fourierCoeff f S) * chiS S x) =
        (fourierCoeff f S * chiS S x) / spectralOneNorm f := by
    rw [hp]
    conv_rhs => rw [← abs_mul_thresholdSign (fourierCoeff f S)]
    ring
  simp_rw [hterm]
  rw [← Finset.sum_div, ← walsh_expansion f x]

end PMFMean

/-- A nonzero Boolean function has positive spectral one-norm, since a function whose Fourier
coefficients all vanish is zero. -/
theorem spectralOneNorm_pos {n : ℕ} {f : BooleanFunc n} (hf : f ≠ 0) :
    0 < spectralOneNorm f := by
  refine (spectralOneNorm_nonneg f).lt_of_ne fun h ↦ hf (funext fun x ↦ ?_)
  have hcoeff (S : Finset (Fin n)) : fourierCoeff f S = 0 :=
    abs_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg fun T _ ↦ abs_nonneg _).mp h.symm S
      (Finset.mem_univ S))
  simp [walsh_expansion f x, hcoeff]

section SignedSample

variable {n : ℕ}
local instance : MeasurableSpace (Finset (Fin n)) := ⊤

/-- A nonzero function of positive arity admits one signed Fourier-character sample of size `s`
whose scaled average is uniformly within `δ` of the function. The positive-arity hypothesis makes
explicit the source's standing convention. [OD14, Thm. 5.12; BS92]

**Proof sketch.** Normalize the absolute Fourier coefficients to a probability distribution.
Independent samples have the correct expectation at each cube point. Hoeffding's inequality
bounds both error tails, and a union bound over all `2ⁿ` points has probability below one under
the stated sample-size hypothesis. Choose a sample outside every bad event and rescale. -/
theorem sparse_signed_sample (f : BooleanFunc n) (hn : 0 < n) (hf : f ≠ 0)
    {δ : ℝ} (hδ : 0 < δ) (s : ℕ)
    (hs : 4 * n * spectralOneNorm f ^ 2 / δ ^ 2 ≤ s) :
    ∃ T : Fin s → Finset (Fin n), ∀ x : BoolCube n,
      |f x - ∑ j : Fin s,
        (spectralOneNorm f / (s : ℝ) * thresholdSign (fourierCoeff f (T j))) *
          chiS (T j) x| < δ := by
  classical
  let L := spectralOneNorm f
  have hL : 0 < L := spectralOneNorm_pos hf
  have hspos : 0 < s := by
    have hbound : 0 < 4 * n * spectralOneNorm f ^ 2 / δ ^ 2 := by positivity
    exact_mod_cast (lt_of_lt_of_le hbound hs)
  obtain ⟨pmf, hpmfmean⟩ := sparse_sample_pmf_mean n f hL
  let μ : Measure (Fin s → Finset (Fin n)) :=
    Measure.pi (fun _ ↦ pmf.toMeasure)
  let Y (x : BoolCube n) (j : Fin s) (ω : Fin s → Finset (Fin n)) : ℝ :=
    thresholdSign (fourierCoeff f (ω j)) * chiS (ω j) x
  let bad (x : BoolCube n) : Set (Fin s → Finset (Fin n)) :=
    {ω | (s : ℝ) * (δ / L) ≤
      |∑ j : Fin s, Y x j ω - (s : ℝ) * (f x / L)|}
  have hbad (x : BoolCube n) :
      μ.real (bad x) ≤ 2 * Real.exp (-(s : ℝ) * (δ / L) ^ 2 / 2) := by
    have hindepCoord :
        iIndepFun (fun j (ω : Fin s → Finset (Fin n)) ↦ ω j) μ :=
      iIndepFun_pi (fun j ↦ aemeasurable_id)
    have hindep : iIndepFun (Y x) μ :=
      hindepCoord.comp
        (fun _ S ↦ thresholdSign (fourierCoeff f S) * chiS S x)
        (fun _ ↦ Measurable.of_discrete)
    have hmeas : ∀ j, AEMeasurable (Y x j) μ := by
      intro j
      change AEMeasurable
        ((fun S : Finset (Fin n) ↦ thresholdSign (fourierCoeff f S) * chiS S x) ∘
          (fun ω : Fin s → Finset (Fin n) ↦ ω j)) μ
      exact (Measurable.of_discrete.comp (measurable_pi_apply j)).aemeasurable
    have hbound : ∀ j, ∀ᵐ ω ∂μ, Y x j ω ∈ Set.Icc (-1 : ℝ) 1 := by
      refine fun j ↦ Filter.Eventually.of_forall fun ω ↦ abs_le.mp ?_
      have hchi : |chiS (ω j) x| = 1 := by
        rcases sq_eq_one_iff.mp (chiS_sq_eq_one (ω j) x) with h | h <;> simp [h]
      simp [Y, abs_mul, hchi]
    have hmean : ∀ j, ∫ ω, Y x j ω ∂μ = f x / L := by
      intro j
      simpa [Y, μ, L] using
        (integral_comp_eval (μ := fun _ : Fin s ↦ pmf.toMeasure)
          (i := j) (f := fun S : Finset (Fin n) ↦
            thresholdSign (fourierCoeff f S) * chiS S x)
          Measurable.of_discrete.aestronglyMeasurable).trans (hpmfmean x)
    exact sample_abs_tail hindep hmeas hbound hmean hspos
      (div_nonneg hδ.le hL.le)
  have hcard : (Fintype.card (BoolCube n) : ℝ) = (2 : ℝ) ^ n := by
    simp [BoolCube]
  have hB : (Fintype.card (BoolCube n) : ℝ) *
      (2 * Real.exp (-(s : ℝ) * (δ / L) ^ 2 / 2)) < 1 := by
    rw [hcard]
    exact sparse_union_numeric n s hn L δ hL hδ hs
  obtain ⟨T, hT⟩ := exists_good_of_union_bound bad hbad hB
  refine ⟨T, ?_⟩
  intro x
  have hsR : 0 < (s : ℝ) := by exact_mod_cast hspos
  have hc : 0 < L / (s : ℝ) := div_pos hL hsR
  -- Rescaling the centred sampled sum by `L / s` gives the approximation error.
  set z : ℝ := ∑ j : Fin s, Y x j T
  have hsum : (∑ j : Fin s,
      (L / (s : ℝ) * thresholdSign (fourierCoeff f (T j))) * chiS (T j) x) = L / (s : ℝ) * z := by
    simp only [z, Y, Finset.mul_sum, mul_assoc]
  have hidentity : f x - L / (s : ℝ) * z = -(L / (s : ℝ)) * (z - (s : ℝ) * (f x / L)) := by
    field_simp
    ring
  have hscale : L / (s : ℝ) * ((s : ℝ) * (δ / L)) = δ := by
    field_simp
  rw [hsum, hidentity, abs_mul, abs_neg, abs_of_pos hc, ← hscale]
  exact mul_lt_mul_of_pos_left (lt_of_not_ge (hT x)) hc

end SignedSample

end BooleanAnalysis.ThresholdFunctions
