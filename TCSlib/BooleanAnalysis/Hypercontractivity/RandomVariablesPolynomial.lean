/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.BooleanAnalysis.Hypercontractivity.RandomVariablesBasic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Fourth moments of multilinear polynomials in independent random variables

## Main definitions

The polynomial evaluation and probability-space definitions are in `RandomVariablesBasic`.

## Main results

* `MultilinearMoments.affine_moments`: second and fourth moments after splitting off an input.
* `MultilinearMoments.cauchy_schwarz`: the bound for the mixed fourth moment.
* `MultilinearMoments.indep_sum_of_notMem`: independence from a pair of polynomial sums.
* `independent_multilinear_reasonable`: the general random-variable form of Corollary 9.6.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014;
  May 2021 arXiv edition, §9.1, especially Corollary 9.6.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace BooleanAnalysis.Hypercontractivity

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/--
For real random variables `A`, `D`, and `X` in `MemLp 4`, with `X` independent
of the joint pair `(A, D)` and `E[X] = E[X³] = 0`, the second moment of
`A + XD` is `E[A²] + E[X²]E[D²]` and its fourth moment is
`E[A⁴] + 6E[X²]E[A²D²] + E[X⁴]E[D⁴]`. [OD14, Cor. 9.6 (proof)]

**Proof sketch.** Expand both powers. The `MemLp` assumptions make every
mixed monomial in `A` and `D` of total degree at most four integrable, as
well as every needed power of `X`. Joint independence factors each mixed
integral into an `X` moment and an `(A, D)` moment. Integrate the expansions
and eliminate the terms containing the first or third moment of `X`.
-/
theorem MultilinearMoments.affine_moments
    {A D X : Ω → ℝ}
    (hA : MemLp A 4 μ)
    (hD : MemLp D 4 μ)
    (hX : MemLp X 4 μ)
    (hXAD : IndepFun X (fun ω => (A ω, D ω)) μ)
    (hX_mean : (∫ ω, X ω ∂μ) = 0)
    (hX_third : (∫ ω, X ω ^ 3 ∂μ) = 0) :
    (∫ ω, (A ω + X ω * D ω) ^ 2 ∂μ) =
        (∫ ω, A ω ^ 2 ∂μ) +
          (∫ ω, X ω ^ 2 ∂μ) * (∫ ω, D ω ^ 2 ∂μ) ∧
      (∫ ω, (A ω + X ω * D ω) ^ 4 ∂μ) =
        (∫ ω, A ω ^ 4 ∂μ) +
          6 * (∫ ω, X ω ^ 2 ∂μ) *
            (∫ ω, A ω ^ 2 * D ω ^ 2 ∂μ) +
          (∫ ω, X ω ^ 4 ∂μ) * (∫ ω, D ω ^ 4 ∂μ) := by
  -- Obtain the required moments and mixed products from the fourth-moment bounds.
  have hXp (j : ℕ) (hj : j ≤ 4) :
      Integrable (fun ω => X ω ^ j) μ := by
    simpa only [pow_zero, mul_one] using
      (integrable_mul_pow_of_memLp (p := 4) (a := j) (b := 0)
        hX hX (by omega))
  have hADp (a b : ℕ) (hab : a + b ≤ 4) :
      Integrable (fun ω => A ω ^ a * D ω ^ b) μ := by
    exact integrable_mul_pow_of_memLp (p := 4) hA hD hab
  have hAp (a : ℕ) (ha : a ≤ 4) :
      Integrable (fun ω => A ω ^ a) μ := by
    simpa only [pow_zero, mul_one] using hADp a 0 (by omega)
  have hInd (j a b : ℕ) :
      IndepFun (fun ω => X ω ^ j)
        (fun ω => A ω ^ a * D ω ^ b) μ := by
    simpa only [Function.comp_apply] using
      hXAD.comp
        (show Measurable (fun x : ℝ => x ^ j) by fun_prop)
        (show Measurable (fun z : ℝ × ℝ => z.1 ^ a * z.2 ^ b) by
          fun_prop)
  have hMix (j a b : ℕ) (hj : j ≤ 4) (hab : a + b ≤ 4) :
      Integrable (fun ω => X ω ^ j * (A ω ^ a * D ω ^ b)) μ := by
    exact (hInd j a b).integrable_mul (hXp j hj) (hADp a b hab)
  have hFactor (j a b : ℕ) (hj : j ≤ 4) (hab : a + b ≤ 4) :
      (∫ ω, X ω ^ j * (A ω ^ a * D ω ^ b) ∂μ) =
        (∫ ω, X ω ^ j ∂μ) * (∫ ω, A ω ^ a * D ω ^ b ∂μ) := by
    exact (hInd j a b).integral_fun_mul_eq_mul_integral
      (hXp j hj).aestronglyMeasurable
      (hADp a b hab).aestronglyMeasurable
  -- Expand each power, integrate its terms, and cancel the odd moments.
  constructor
  · calc
      (∫ ω, (A ω + X ω * D ω) ^ 2 ∂μ) =
          (∫ ω, A ω ^ 2 +
            2 * (X ω ^ 1 * (A ω ^ 1 * D ω ^ 1)) +
            X ω ^ 2 * (A ω ^ 0 * D ω ^ 2) ∂μ) := by
              apply integral_congr_ae
              filter_upwards [] with ω
              ring
      _ = (∫ ω, A ω ^ 2 ∂μ) +
          2 * (∫ ω, X ω ^ 1 * (A ω ^ 1 * D ω ^ 1) ∂μ) +
          (∫ ω, X ω ^ 2 * (A ω ^ 0 * D ω ^ 2) ∂μ) := by
            rw [integral_add
              (f := fun ω => A ω ^ 2 +
                2 * (X ω ^ 1 * (A ω ^ 1 * D ω ^ 1)))
              (g := fun ω => X ω ^ 2 * (A ω ^ 0 * D ω ^ 2))
              ((hAp 2 (by omega)).add
                ((hMix 1 1 1 (by omega) (by omega)).const_mul 2))
              (hMix 2 0 2 (by omega) (by omega)),
              integral_add
                (f := fun ω => A ω ^ 2)
                (g := fun ω => 2 * (X ω ^ 1 * (A ω ^ 1 * D ω ^ 1)))
                (hAp 2 (by omega))
                ((hMix 1 1 1 (by omega) (by omega)).const_mul 2)]
            simp only [integral_const_mul]
      _ = (∫ ω, A ω ^ 2 ∂μ) +
          (∫ ω, X ω ^ 2 ∂μ) * (∫ ω, D ω ^ 2 ∂μ) := by
            rw [hFactor 1 1 1 (by omega) (by omega),
              hFactor 2 0 2 (by omega) (by omega)]
            simp [hX_mean]
  · calc
      (∫ ω, (A ω + X ω * D ω) ^ 4 ∂μ) =
          (∫ ω, A ω ^ 4 +
            4 * (X ω ^ 1 * (A ω ^ 3 * D ω ^ 1)) +
            6 * (X ω ^ 2 * (A ω ^ 2 * D ω ^ 2)) +
            4 * (X ω ^ 3 * (A ω ^ 1 * D ω ^ 3)) +
            X ω ^ 4 * (A ω ^ 0 * D ω ^ 4) ∂μ) := by
              apply integral_congr_ae
              filter_upwards [] with ω
              ring
      _ = (∫ ω, A ω ^ 4 ∂μ) +
          4 * (∫ ω, X ω ^ 1 * (A ω ^ 3 * D ω ^ 1) ∂μ) +
          6 * (∫ ω, X ω ^ 2 * (A ω ^ 2 * D ω ^ 2) ∂μ) +
          4 * (∫ ω, X ω ^ 3 * (A ω ^ 1 * D ω ^ 3) ∂μ) +
          (∫ ω, X ω ^ 4 * (A ω ^ 0 * D ω ^ 4) ∂μ) := by
            rw [integral_add
              (f := fun ω => A ω ^ 4 +
                4 * (X ω ^ 1 * (A ω ^ 3 * D ω ^ 1)) +
                6 * (X ω ^ 2 * (A ω ^ 2 * D ω ^ 2)) +
                4 * (X ω ^ 3 * (A ω ^ 1 * D ω ^ 3)))
              (g := fun ω => X ω ^ 4 * (A ω ^ 0 * D ω ^ 4))
              ((((hAp 4 (by omega)).add
                ((hMix 1 3 1 (by omega) (by omega)).const_mul 4)).add
                ((hMix 2 2 2 (by omega) (by omega)).const_mul 6)).add
                ((hMix 3 1 3 (by omega) (by omega)).const_mul 4))
              (hMix 4 0 4 (by omega) (by omega)),
              integral_add
                (f := fun ω => A ω ^ 4 +
                  4 * (X ω ^ 1 * (A ω ^ 3 * D ω ^ 1)) +
                  6 * (X ω ^ 2 * (A ω ^ 2 * D ω ^ 2)))
                (g := fun ω => 4 * (X ω ^ 3 * (A ω ^ 1 * D ω ^ 3)))
                (((hAp 4 (by omega)).add
                  ((hMix 1 3 1 (by omega) (by omega)).const_mul 4)).add
                  ((hMix 2 2 2 (by omega) (by omega)).const_mul 6))
                ((hMix 3 1 3 (by omega) (by omega)).const_mul 4),
              integral_add
                (f := fun ω => A ω ^ 4 +
                  4 * (X ω ^ 1 * (A ω ^ 3 * D ω ^ 1)))
                (g := fun ω => 6 * (X ω ^ 2 * (A ω ^ 2 * D ω ^ 2)))
                ((hAp 4 (by omega)).add
                  ((hMix 1 3 1 (by omega) (by omega)).const_mul 4))
                ((hMix 2 2 2 (by omega) (by omega)).const_mul 6),
              integral_add
                (f := fun ω => A ω ^ 4)
                (g := fun ω => 4 * (X ω ^ 1 * (A ω ^ 3 * D ω ^ 1)))
                (hAp 4 (by omega))
                ((hMix 1 3 1 (by omega) (by omega)).const_mul 4)]
            simp only [integral_const_mul]
      _ = (∫ ω, A ω ^ 4 ∂μ) +
          6 * (∫ ω, X ω ^ 2 ∂μ) *
            (∫ ω, A ω ^ 2 * D ω ^ 2 ∂μ) +
          (∫ ω, X ω ^ 4 ∂μ) * (∫ ω, D ω ^ 4 ∂μ) := by
            rw [hFactor 1 3 1 (by omega) (by omega),
              hFactor 2 2 2 (by omega) (by omega),
              hFactor 3 1 3 (by omega) (by omega),
              hFactor 4 0 4 (by omega) (by omega)]
            simp [hX_mean, hX_third, mul_assoc]

/--
For two real variables in `L⁴`, the square of the integral of their squared
product is at most the product of their fourth-moment integrals.
This generalizes the source's probability-space setting to arbitrary measures,
since finite fourth moments suffice.

[OD14, Cor. 9.6 (proof)]

**Proof sketch.** Finite fourth moments make the squared variables
square-integrable. Apply Cauchy–Schwarz to these squared variables. Square the
resulting nonnegative inequality and simplify the square roots of the
nonnegative fourth moments.
-/
theorem MultilinearMoments.cauchy_schwarz {μ : Measure Ω} {A D : Ω → ℝ}
    (hA : MemLp A 4 μ) (hD : MemLp D 4 μ) :
    (∫ ω, (A ω) ^ 2 * (D ω) ^ 2 ∂μ) ^ 2 ≤
      (∫ ω, (A ω) ^ 4 ∂μ) * (∫ ω, (D ω) ^ 4 ∂μ) := by
  have hA2 : MemLp (fun ω => (A ω) ^ 2) (ENNReal.ofReal (2 : ℝ)) μ := by
    convert hA.norm_rpow_div (2 : ℝ≥0∞) using 1 <;>
      norm_num [Real.norm_eq_abs, Real.rpow_two, sq_abs]
    simpa only [show (2 : ℝ≥0∞) * 2 = 4 from by norm_num] using
      (ENNReal.mul_div_cancel_right (a := (2 : ℝ≥0∞))
        (b := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)).symm
  have hD2 : MemLp (fun ω => (D ω) ^ 2) (ENNReal.ofReal (2 : ℝ)) μ := by
    convert hD.norm_rpow_div (2 : ℝ≥0∞) using 1 <;>
      norm_num [Real.norm_eq_abs, Real.rpow_two, sq_abs]
    simpa only [show (2 : ℝ≥0∞) * 2 = 4 from by norm_num] using
      (ENNReal.mul_div_cancel_right (a := (2 : ℝ≥0∞))
        (b := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)).symm
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg
    (p := (2 : ℝ)) (q := (2 : ℝ))
    (by norm_num [Real.holderConjugate_iff])
    (Filter.Eventually.of_forall (fun ω => sq_nonneg (A ω)))
    (Filter.Eventually.of_forall (fun ω => sq_nonneg (D ω)))
    hA2 hD2
  have hbound :
      (∫ ω, (A ω) ^ 2 * (D ω) ^ 2 ∂μ) ≤
        Real.sqrt (∫ ω, (A ω) ^ 4 ∂μ) *
          Real.sqrt (∫ ω, (D ω) ^ 4 ∂μ) := by
    simpa only [Real.rpow_two, ← pow_mul,
      show (2 : ℕ) * 2 = 4 from rfl, ← Real.sqrt_eq_rpow] using hCS
  calc
    (∫ ω, (A ω) ^ 2 * (D ω) ^ 2 ∂μ) ^ 2 ≤
        (Real.sqrt (∫ ω, (A ω) ^ 4 ∂μ) *
          Real.sqrt (∫ ω, (D ω) ^ 4 ∂μ)) ^ 2 :=
      pow_le_pow_left₀
        (integral_nonneg (fun ω => mul_nonneg (sq_nonneg (A ω)) (sq_nonneg (D ω))))
        hbound 2
    _ = (∫ ω, (A ω) ^ 4 ∂μ) * (∫ ω, (D ω) ^ 4 ∂μ) := by
      rw [mul_pow,
        Real.sq_sqrt (show 0 ≤ (∫ ω, (A ω) ^ 4 ∂μ) from
          integral_nonneg (fun ω => by positivity)),
        Real.sq_sqrt (show 0 ≤ (∫ ω, (D ω) ^ 4 ∂μ) from
          integral_nonneg (fun ω => by positivity))]

/-- A coordinate outside `s` is independent of the joint pair of multilinear
polynomial sums supported on `s`.

This isolates the independence argument in [OD14, Cor. 9.6 (proof)] and
generalizes it from the source probability space to arbitrary measures, assuming
joint independence and almost-everywhere measurability of the coordinates.

**Proof sketch.** The singleton coordinate family indexed by `{i}` and the
coordinate family indexed by `s` are independent because their index sets are
disjoint. Compose the first family with evaluation at `i` and the second with
the measurable map producing the pair of polynomial sums. Extend the latter
tuple by zero outside `s`. Every monomial index belongs to a subset of `s`, so
this extension reproduces both sums. Their joint map is measurable because
finite sums and products of coordinate maps are measurable.
-/
theorem MultilinearMoments.indep_sum_of_notMem
    {μ : Measure Ω} {n : ℕ} {X : Fin n → Ω → ℝ}
    (hX : iIndepFun X μ)
    (hXm : ∀ j, AEMeasurable (X j) μ)
    (F G : ThresholdFunctions.MultilinearPolynomial n)
    (s : Finset (Fin n)) (i : Fin n) (hi : i ∉ s) :
    IndepFun (X i)
      (fun ω ↦
        ((∑ T ∈ s.powerset, F T * ∏ j ∈ T, X j ω),
         (∑ T ∈ s.powerset, G T * ∏ j ∈ T, X j ω))) μ := by
  classical
  -- Extend the tuple on s by zero, then evaluate each polynomial.
  let P (H : ThresholdFunctions.MultilinearPolynomial n) (y : s → ℝ) : ℝ :=
    ∑ T ∈ s.powerset, H T *
      ∏ j ∈ T, if hj : j ∈ s then y ⟨j, hj⟩ else 0
  have hcoord (j : Fin n) :
      Measurable (fun y : s → ℝ ↦ if hj : j ∈ s then y ⟨j, hj⟩ else 0) := by
    by_cases hj : j ∈ s
    · simpa only [dif_pos hj] using
        (measurable_pi_apply (⟨j, hj⟩ : s))
    · simp only [dif_neg hj]
      exact measurable_const
  have hP (H : ThresholdFunctions.MultilinearPolynomial n) : Measurable (P H) := by
    dsimp only [P]
    exact Finset.measurable_fun_sum s.powerset
      (fun T _ ↦ measurable_const.mul
        (Finset.measurable_fun_prod T (fun j _ ↦ hcoord j)))
  have hP_eval (H : ThresholdFunctions.MultilinearPolynomial n) :
      (fun ω ↦ P H (fun j : s ↦ X j ω)) =
        (fun ω ↦ ∑ T ∈ s.powerset, H T * ∏ j ∈ T, X j ω) := by
    funext ω
    dsimp only [P]
    apply Finset.sum_congr rfl
    intro T hT
    apply congrArg (fun z : ℝ ↦ H T * z)
    apply Finset.prod_congr rfl
    intro j hj
    simp only [dif_pos (Finset.mem_powerset.mp hT hj)]
  -- Compose independence of the disjoint tuples with measurable evaluation.
  have hdisj : Disjoint ({i} : Finset (Fin n)) s :=
    Finset.disjoint_singleton_left.mpr hi
  have hind := iIndepFun.indepFun_finset₀
    ({i} : Finset (Fin n)) s hdisj hX hXm
  have hcomp := hind.comp
    (measurable_pi_apply
      (⟨i, Finset.mem_singleton_self i⟩ : ({i} : Finset (Fin n))))
    ((hP F).prodMk (hP G))
  have heval :
      (fun y : s → ℝ ↦ (P F y, P G y)) ∘
          (fun ω (j : s) ↦ X j ω) =
        (fun ω ↦
          ((∑ T ∈ s.powerset, F T * ∏ j ∈ T, X j ω),
           (∑ T ∈ s.powerset, G T * ∏ j ∈ T, X j ω))) := by
    funext ω
    exact Prod.ext (congrFun (hP_eval F) ω) (congrFun (hP_eval G) ω)
  rw [heval] at hcomp
  simpa only [Function.comp_def] using hcomp

/-- A degree-`k` multilinear polynomial in independent `B`-reasonable inputs with
vanishing first and third moments is `max(B,9)^k`-reasonable. Explicit finite fourth moments
exclude totalized nonintegrable moments. [OD14, Cor. 9.6]

**Proof sketch.** Induct on the number of inputs and split off the last variable.
Independence and vanishing odd moments eliminate odd mixed terms. Bound the mixed fourth
moment by Cauchy–Schwarz and close the recurrence with the constant `max(B,9)`. -/
theorem independent_multilinear_reasonable {n k : ℕ}
    (F : ThresholdFunctions.MultilinearPolynomial n) (X : Fin n → Ω → ℝ) (B : ℝ) (hB : 1 ≤ B)
    (hdegree : F.HasDegreeAtMost k) (hindep : iIndepFun X μ)
    (hmem : ∀ i, MemLp (X i) 4 μ) (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hthird : ∀ i, ∫ ω, X i ω ^ 3 ∂μ = 0)
    (hreasonable : ∀ i, Bonami.IsBReasonable (X i) μ B) :
    MemLp (evalMultilinearRV F X) 4 μ ∧
      Bonami.IsBReasonable (evalMultilinearRV F X) μ ((max B 9) ^ k) := by
  classical
  let R : ℝ := max B 9
  let Y (s : Finset (Fin n)) (H : ThresholdFunctions.MultilinearPolynomial n) :
      Ω → ℝ := fun ω => ∑ T ∈ s.powerset, H T * ∏ j ∈ T, X j ω
  have hR : 9 ≤ R := le_max_right B 9
  have hRone : 1 ≤ R := le_trans (by norm_num) hR
  have hRzero : 0 ≤ R := le_trans (by norm_num) hR
  have hYmem (s : Finset (Fin n)) (H : ThresholdFunctions.MultilinearPolynomial n) :
      MemLp (Y s H) 4 μ := by
    let J : ThresholdFunctions.MultilinearPolynomial n := fun T =>
      if T ⊆ s then H T else 0
    have hfilter :
        (Finset.univ : Finset (Finset (Fin n))).filter (fun T => T ⊆ s) =
          s.powerset := by
      ext T
      simp [Finset.mem_powerset]
    have hEq : evalMultilinearRV J X = Y s H := by
      funext ω
      change (∑ T : Finset (Fin n), (if T ⊆ s then H T else 0) *
          ∏ j ∈ T, X j ω) =
        ∑ T ∈ s.powerset, H T * ∏ j ∈ T, X j ω
      simp_rw [ite_mul, zero_mul]
      rw [← Finset.sum_filter, hfilter]
    rw [← hEq]
    exact evalMultilinearRV_memLp J X μ hindep hmem
  have hconstant (c : ℝ) (m : ℕ) :
      (∫ ω : Ω, c ^ 4 ∂μ) ≤ R ^ m * (∫ ω : Ω, c ^ 2 ∂μ) ^ 2 := by
    have hc : c ^ 4 = (c ^ 2) ^ 2 := by ring
    simpa [integral_const, hc] using
      mul_le_mul_of_nonneg_right
        (one_le_pow₀ hRone : 1 ≤ R ^ m) (sq_nonneg (c ^ 2))
  have hYconst (s : Finset (Fin n)) (H : ThresholdFunctions.MultilinearPolynomial n)
      (hH : H.HasDegreeAtMost 0) : Y s H = fun _ => H ∅ := by
    funext ω
    change (∑ T ∈ s.powerset, H T * ∏ j ∈ T, X j ω) = H ∅
    rw [Finset.sum_eq_single ∅]
    · simp
    · intro T hT hTne
      have hcard : 0 < T.card := Nat.pos_of_ne_zero (by
        intro hcard
        exact hTne (Finset.card_eq_zero.mp hcard))
      rw [hH T hcard, zero_mul]
    · simp
  -- Induct over the active coordinates, keeping the ambient index type fixed.
  have hYbound : ∀ (s : Finset (Fin n)) (m : ℕ)
      (H : ThresholdFunctions.MultilinearPolynomial n), H.HasDegreeAtMost m →
      (∫ ω, Y s H ω ^ 4 ∂μ) ≤ R ^ m * (∫ ω, Y s H ω ^ 2 ∂μ) ^ 2 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro m H hH
        simpa [Y] using hconstant (H ∅) m
    | @insert i s hi ih =>
        intro m H hH
        cases m with
        | zero =>
            rw [hYconst (insert i s) H hH]
            exact hconstant (H ∅) 0
        | succ m =>
            let G : ThresholdFunctions.MultilinearPolynomial n := fun T =>
              if i ∈ T then 0 else H (insert i T)
            have hG : G.HasDegreeAtMost m := by
              intro T hT
              dsimp only [G]
              by_cases hiT : i ∈ T
              · simp only [if_pos hiT]
              · rw [if_neg hiT]
                apply hH
                simpa only [Finset.card_insert_of_notMem hiT] using
                  Nat.succ_lt_succ hT
            let A : Ω → ℝ := Y s H
            let D : Ω → ℝ := Y s G
            have hAmem : MemLp A 4 μ := hYmem s H
            have hDmem : MemLp D 4 μ := hYmem s G
            have hsplit : Y (insert i s) H = fun ω => A ω + X i ω * D ω := by
              funext ω
              have hGsum :
                  (∑ T ∈ s.powerset, G T * ∏ j ∈ T, X j ω) =
                    ∑ T ∈ s.powerset, H (insert i T) * ∏ j ∈ T, X j ω := by
                apply Finset.sum_congr rfl
                intro T hT
                have hiT : i ∉ T := by
                  intro hiT
                  exact hi ((Finset.mem_powerset.mp hT) hiT)
                simp only [G, if_neg hiT]
              dsimp only [Y, A, D]
              rw [multilinear_sum_insert hi H X ω, hGsum]
            have hXAD : IndepFun (X i) (fun ω => (A ω, D ω)) μ :=
              MultilinearMoments.indep_sum_of_notMem hindep
                (fun j => (hmem j).aemeasurable) H G s i hi
            obtain ⟨hsecond, hfourth⟩ :=
              MultilinearMoments.affine_moments hAmem hDmem (hmem i)
                hXAD (hmean i) (hthird i)
            let t : ℝ := R ^ m
            let a : ℝ := ∫ ω, A ω ^ 2 ∂μ
            let d : ℝ := ∫ ω, D ω ^ 2 ∂μ
            let v : ℝ := ∫ ω, X i ω ^ 2 ∂μ
            let w : ℝ := ∫ ω, X i ω ^ 4 ∂μ
            let M_A : ℝ := ∫ ω, A ω ^ 4 ∂μ
            let M_D : ℝ := ∫ ω, D ω ^ 4 ∂μ
            let C : ℝ := ∫ ω, A ω ^ 2 * D ω ^ 2 ∂μ
            have ht : 0 ≤ t := pow_nonneg hRzero m
            have htsqrt : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt ht
            have ha : 0 ≤ a := integral_nonneg (fun ω => sq_nonneg (A ω))
            have hd : 0 ≤ d := integral_nonneg (fun ω => sq_nonneg (D ω))
            have hv : 0 ≤ v := integral_nonneg (fun ω => sq_nonneg (X i ω))
            have hMD : 0 ≤ M_D := integral_nonneg (fun ω => by positivity)
            have hC : 0 ≤ C := integral_nonneg (fun ω =>
              mul_nonneg (sq_nonneg (A ω)) (sq_nonneg (D ω)))
            have hA_bound : M_A ≤ R * t * a ^ 2 := by
              calc
                M_A ≤ R ^ (m + 1) * a ^ 2 := ih (m + 1) H hH
                _ = R * t * a ^ 2 := by
                  dsimp only [t]
                  rw [pow_succ]
                  ring
            have hD_bound : M_D ≤ t * d ^ 2 := ih m G hG
            have hw : w ≤ R * v ^ 2 := by
              have hwB : w ≤ B * v ^ 2 := by
                simpa only [ProbabilityTheory.moment, Pi.pow_apply] using
                  (hreasonable i).moment_le
              exact hwB.trans
                (mul_le_mul_of_nonneg_right (le_max_left B 9) (sq_nonneg v))
            have hCS : C ^ 2 ≤ M_A * M_D :=
              MultilinearMoments.cauchy_schwarz hAmem hDmem
            -- Scale the moment bounds to apply the scalar affine inequality.
            have hscaledA : M_A ≤ R * (Real.sqrt t * a) ^ 2 := by
              calc
                M_A ≤ R * t * a ^ 2 := hA_bound
                _ = R * (Real.sqrt t * a) ^ 2 := by
                  simp only [mul_pow, htsqrt]
                  ring
            have hscaledD : v ^ 2 * M_D ≤ (Real.sqrt t * v * d) ^ 2 := by
              calc
                v ^ 2 * M_D ≤ v ^ 2 * (t * d ^ 2) :=
                  mul_le_mul_of_nonneg_left hD_bound (sq_nonneg v)
                _ = (Real.sqrt t * v * d) ^ 2 := by
                  simp only [mul_pow, htsqrt]
                  ring
            have hscaledC : (v * C) ^ 2 ≤ M_A * (v ^ 2 * M_D) := by
              calc
                (v * C) ^ 2 = v ^ 2 * C ^ 2 := by ring
                _ ≤ v ^ 2 * (M_A * M_D) :=
                  mul_le_mul_of_nonneg_left hCS (sq_nonneg v)
                _ = M_A * (v ^ 2 * M_D) := by ring
            have hstep := reasonable_moment_algebra R
              (Real.sqrt t * a) (Real.sqrt t * v * d)
              M_A (v ^ 2 * M_D) (v * C) hR
              (mul_nonneg (Real.sqrt_nonneg t) ha)
              (mul_nonneg (mul_nonneg (Real.sqrt_nonneg t) hv) hd)
              (mul_nonneg hv hC)
              (mul_nonneg (sq_nonneg v) hMD)
              hscaledA hscaledD hscaledC
            have halgebra :
                M_A + 6 * v * C + R * v ^ 2 * M_D ≤
                  R * t * (a + v * d) ^ 2 := by
              calc
                M_A + 6 * v * C + R * v ^ 2 * M_D =
                    M_A + 6 * (v * C) + R * (v ^ 2 * M_D) := by ring
                _ ≤ R * (Real.sqrt t * a + Real.sqrt t * v * d) ^ 2 := hstep
                _ = R * t * (a + v * d) ^ 2 := by
                  rw [show Real.sqrt t * a + Real.sqrt t * v * d =
                    Real.sqrt t * (a + v * d) by ring]
                  simp only [mul_pow, htsqrt]
                  ring
            rw [hsplit, hfourth, hsecond]
            change M_A + 6 * v * C + w * M_D ≤
              R ^ (m + 1) * (a + v * d) ^ 2
            calc
              M_A + 6 * v * C + w * M_D ≤
                  M_A + 6 * v * C + (R * v ^ 2) * M_D :=
                add_le_add_left (mul_le_mul_of_nonneg_right hw hMD) _
              _ ≤ R * t * (a + v * d) ^ 2 := halgebra
              _ = R ^ (m + 1) * (a + v * d) ^ 2 := by
                dsimp only [t]
                rw [pow_succ]
                ring
  have hmemF := evalMultilinearRV_memLp F X μ hindep hmem
  refine ⟨hmemF, ?_⟩
  refine ⟨inferInstance, one_le_pow₀ hRone, hmemF, ?_⟩
  simpa only [ProbabilityTheory.moment, Pi.pow_apply, Y, Finset.powerset_univ,
    evalMultilinearRV, R] using hYbound Finset.univ k F hdegree


end BooleanAnalysis.Hypercontractivity
