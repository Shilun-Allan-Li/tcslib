import TCSlib.BooleanAnalysis.Hypercontractivity
import TCSlib.BooleanAnalysis.Basic
import TCSlib.BooleanAnalysis.Bonami
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Lebesgue.Norm
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.MeanInequalities -- This imports the Real conjugate exponent API
import Mathlib.Data.Real.Sign
/-
# One-Bit (p, 2)-Hypercontractivity

This file proves the (p, 2)-hypercontractivity theorem for functions on a single bit,
following the proof in O'Donnell's *Analysis of Boolean Functions*.

## Main results
- `(p, 2)-hypercontractivity on a single bit`:
  For f : BoolCube 1 → ℝ, 1 ≤ p ≤ 2, and 0 ≤ ρ with ρ² ≤ p − 1:
  (𝔼[(T_ρ f)²])^{1/2} ≤ (𝔼[|f|^p])^{1/p}
- `(2, q)-hypercontractivity on a single bit`:
  For g : BoolCube 1 → ℝ and q ≥ 2:
  ‖T_{1 / √(q - 1)} g‖_q ≤ ‖g‖_2


-/

set_option maxHeartbeats 1600000

namespace OneBitHypercontractivity

open BooleanAnalysis Real Bonami

/-! ## Enumeration helpers for BoolCube 1 and Finset (Fin 1) -/

private lemma boolCube1_univ :
    (Finset.univ : Finset (BoolCube 1)) =
    {fun _ => false, fun _ => true} := by decide

private lemma finsetFin1_univ :
    (Finset.univ : Finset (Finset (Fin 1))) = {∅, {0}} := by decide

private lemma boolCube1_ne :
    (fun _ : Fin 1 => false) ≠ (fun _ : Fin 1 => true) := by decide

private lemma finsetFin1_ne : (∅ : Finset (Fin 1)) ≠ {0} := by decide

/-! ## One-bit function values in terms of Fourier coefficients -/

/-- For n=1, f(false) = f̂(∅) + f̂({0}). -/
lemma one_bit_val_false (f : BooleanFunc 1) :
    f (fun _ => false) = fourierCoeff f ∅ + fourierCoeff f {⟨0, by omega⟩} := by
  conv_lhs => rw [walsh_expansion f]
  conv_lhs => rw [show (Finset.univ : Finset (Finset (Fin 1))) = {∅, {0}} from finsetFin1_univ]
  rw [Finset.sum_pair finsetFin1_ne]
  simp [chiS, boolToSign]

/-- For n=1, f(true) = f̂(∅) - f̂({0}). -/
lemma one_bit_val_true (f : BooleanFunc 1) :
    f (fun _ => true) = fourierCoeff f ∅ - fourierCoeff f {⟨0, by omega⟩} := by
  conv_lhs => rw [walsh_expansion f]
  conv_lhs => rw [show (Finset.univ : Finset (Finset (Fin 1))) = {∅, {0}} from finsetFin1_univ]
  rw [Finset.sum_pair finsetFin1_ne]
  simp [chiS, boolToSign]; ring

/-! ## L² norm of T_ρ f for one bit -/

/-- For one-bit functions, 𝔼[(T_ρ f)²] = f̂(∅)² + ρ²f̂({0})². -/
lemma expect_noiseOp_sq_one_bit (ρ : ℝ) (f : BooleanFunc 1) :
    BooleanAnalysis.expect (fun x => (noiseOp ρ f x) ^ 2) =
    (fourierCoeff f ∅) ^ 2 + ρ ^ 2 * (fourierCoeff f {⟨0, by omega⟩}) ^ 2 := by
  rw [show BooleanAnalysis.expect (fun x => (noiseOp ρ f x) ^ 2) =
    innerProduct (noiseOp ρ f) (noiseOp ρ f) from by
    unfold innerProduct; congr 1; ext x; ring]
  rw [parseval (noiseOp ρ f)]
  simp only [noiseOp_fourier]
  conv_lhs => rw [show (Finset.univ : Finset (Finset (Fin 1))) = {∅, {0}} from finsetFin1_univ]
  rw [Finset.sum_pair finsetFin1_ne]
  simp [Finset.card_empty]; ring

/-! ## Lp norm of f for one bit -/

/-- For one-bit functions, 𝔼[|f|^p] = (|a+b|^p + |a-b|^p)/2 where a = f̂(∅), b = f̂({0}). -/
lemma expect_abs_rpow_one_bit (p : ℝ) (f : BooleanFunc 1) :
    BooleanAnalysis.expect (fun x => |f x| ^ p) =
    (|fourierCoeff f ∅ + fourierCoeff f {⟨0, by omega⟩}| ^ p +
     |fourierCoeff f ∅ - fourierCoeff f {⟨0, by omega⟩}| ^ p) / 2 := by
  unfold BooleanAnalysis.expect uniformWeight
  conv_lhs => rw [show (Finset.univ : Finset (BoolCube 1)) = {fun _ => false, fun _ => true}
    from boolCube1_univ]
  rw [Finset.sum_pair boolCube1_ne]
  simp only [one_bit_val_false, one_bit_val_true]
  norm_num; ring

/-! ## The two-point inequality -/

/-
**Two-Point Inequality** (core real inequality, restricted version).
For 1 ≤ p ≤ 2, 0 ≤ b ≤ 1:
  (1 + (p−1)b²)^{p/2} ≤ ((1+b)^p + (1−b)^p) / 2
-/
theorem two_point_ineq_unit (b p : ℝ) (hp1 : 1 ≤ p) (hp2 : p ≤ 2)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    (1 + (p - 1) * b ^ 2) ^ (p / 2) ≤ ((1 + b) ^ p + (1 - b) ^ p) / 2 := by
  -- By the properties of the function $f(b) = \frac{(1+b)^p + (1-b)^p}{2} - (1 + (p-1)b^2)^{p/2}$, we know that $f(0) = 0$ and $f(1) = 2^{p-1} - p^{p/2}$.
  set f : ℝ → ℝ := fun b => ((1 + b)^p + (1 - b)^p) / 2 - (1 + (p - 1) * b^2)^(p / 2);
  -- We need to show that $f(b) \geq 0$ for $0 \leq b \leq 1$.
  have h_f_nonneg : ∀ b ∈ Set.Icc 0 1, f b ≥ 0 := by
    have h_f_deriv_nonneg : ∀ b ∈ Set.Ioo 0 1, 0 ≤ deriv f b := by
      -- Let's calculate the derivative of $f(b)$.
      have h_deriv : ∀ b ∈ Set.Ioo 0 1, deriv f b = p * ((1 + b)^(p-1) - (1 - b)^(p-1)) / 2 - p * (p - 1) * b * (1 + (p - 1) * b^2)^(p / 2 - 1) := by
        intro b hb; norm_num [ add_comm, show b + 1 ≠ 0 from by linarith [ hb.1 ], show b - 1 ≠ 0 from by linarith [ hb.2 ], show p ≠ 0 from by linarith, show p / 2 ≠ 0 from by linarith, show 1 + ( p - 1 ) * b ^ 2 ≠ 0 from by nlinarith [ hb.1, hb.2, show p - 1 ≥ 0 from by linarith ] ] ; ring_nf;
        convert HasDerivAt.deriv ( HasDerivAt.sub ( HasDerivAt.div_const ( HasDerivAt.add ( HasDerivAt.rpow_const ( hasDerivAt_id' b |> HasDerivAt.const_add _ ) _ ) ( HasDerivAt.rpow_const ( hasDerivAt_id' b |> HasDerivAt.const_sub _ ) _ ) ) _ ) ( HasDerivAt.rpow_const ( HasDerivAt.add ( hasDerivAt_const _ _ ) ( HasDerivAt.mul ( hasDerivAt_const _ _ ) ( hasDerivAt_pow 2 b ) ) ) _ ) ) using 1 <;> norm_num <;> ring_nf;
        · exact Or.inl <| by linarith [ hb.1 ] ;
        · exact Or.inl <| by linarith [ hb.1, hb.2 ] ;
        · exact Or.inl ( by nlinarith [ hb.1, hb.2, mul_nonneg ( sub_nonneg.2 hp1 ) ( sq_nonneg b ) ] );
      -- We'll use the fact that $(1 + b)^{p-1} - (1 - b)^{p-1} \geq 2(p-1)b$ for $0 < b < 1$ and $1 \leq p \leq 2$.
      have h_ineq : ∀ b ∈ Set.Ioo 0 1, (1 + b)^(p-1) - (1 - b)^(p-1) ≥ 2 * (p - 1) * b := by
        -- Let's choose any $b \in (0, 1)$ and derive a contradiction to the inequality.
        intro b hb
        have h_deriv_nonneg : ∀ x ∈ Set.Ioo 0 b, 0 ≤ deriv (fun x => (1 + x)^(p-1) - (1 - x)^(p-1) - 2 * (p - 1) * x) x := by
          intros x hx
          have h_deriv : deriv (fun x => (1 + x)^(p-1) - (1 - x)^(p-1) - 2 * (p - 1) * x) x = (p - 1) * ((1 + x)^(p-2) + (1 - x)^(p-2)) - 2 * (p - 1) := by
            convert HasDerivAt.deriv ( HasDerivAt.sub ( HasDerivAt.sub ( HasDerivAt.rpow_const ( hasDerivAt_id' x |> HasDerivAt.const_add _ ) _ ) ( HasDerivAt.rpow_const ( hasDerivAt_id' x |> HasDerivAt.const_sub _ ) _ ) ) ( HasDerivAt.const_mul _ ( hasDerivAt_id' x ) ) ) using 1 <;> norm_num <;> ring_nf;
            · exact Or.inl <| by linarith [ hx.1 ] ;
            · exact Or.inl <| by linarith [ hx.1, hx.2, hb.1, hb.2 ] ;
          have h_ineq : (1 + x)^(p-2) + (1 - x)^(p-2) ≥ 2 := by
            have h_ineq : (1 + x)^(p-2) + (1 - x)^(p-2) ≥ 2 * ((1 + x) * (1 - x))^((p-2)/2) := by
              rw [ Real.mul_rpow ( by linarith [ hx.1, hx.2, hb.1, hb.2 ] ) ( by linarith [ hx.1, hx.2, hb.1, hb.2 ] ) ];
              rw [ show ( 1 + x ) ^ ( p - 2 ) = ( ( 1 + x ) ^ ( ( p - 2 ) / 2 ) ) ^ 2 by rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by linarith [ hx.1, hx.2, hb.1, hb.2 ] ) ] ; ring_nf, show ( 1 - x ) ^ ( p - 2 ) = ( ( 1 - x ) ^ ( ( p - 2 ) / 2 ) ) ^ 2 by rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by linarith [ hx.1, hx.2, hb.1, hb.2 ] ) ] ; ring_nf ] ; nlinarith only [ sq_nonneg ( ( 1 + x ) ^ ( ( p - 2 ) / 2 ) - ( 1 - x ) ^ ( ( p - 2 ) / 2 ) ) ] ;
            exact le_trans ( by exact le_mul_of_one_le_right ( by norm_num ) ( Real.one_le_rpow_of_pos_of_le_one_of_nonpos ( by nlinarith [ hx.1, hx.2, hb.1, hb.2 ] ) ( by nlinarith [ hx.1, hx.2, hb.1, hb.2 ] ) ( by linarith ) ) ) h_ineq;
          nlinarith;
        -- Apply the Mean Value Theorem to the interval [0, b].
        obtain ⟨c, hc⟩ : ∃ c ∈ Set.Ioo 0 b, deriv (fun x => (1 + x)^(p-1) - (1 - x)^(p-1) - 2 * (p - 1) * x) c = ( (1 + b)^(p-1) - (1 - b)^(p-1) - 2 * (p - 1) * b - ( (1 + 0)^(p-1) - (1 - 0)^(p-1) - 2 * (p - 1) * 0 ) ) / (b - 0) := by
          apply_rules [ exists_deriv_eq_slope ];
          · linarith [ hb.1 ];
          · exact continuousOn_of_forall_continuousAt fun x hx => by exact ContinuousAt.sub ( ContinuousAt.sub ( ContinuousAt.rpow ( continuousAt_const.add continuousAt_id ) continuousAt_const <| Or.inl <| by linarith [ hx.1 ] ) ( ContinuousAt.rpow ( continuousAt_const.sub continuousAt_id ) continuousAt_const <| Or.inl <| by linarith [ hx.2, hb.2 ] ) ) ( ContinuousAt.mul continuousAt_const continuousAt_id ) ;
          · exact DifferentiableOn.sub ( DifferentiableOn.sub ( DifferentiableOn.rpow ( differentiableOn_id.const_add _ ) ( differentiableOn_const _ ) ( by intro x hx; linarith [ hx.1 ] ) ) ( DifferentiableOn.rpow ( differentiableOn_id.const_sub _ ) ( differentiableOn_const _ ) ( by intro x hx; linarith [ hx.1, hx.2, hb.2 ] ) ) ) ( DifferentiableOn.mul ( differentiableOn_const _ ) ( differentiableOn_id ) );
        have := h_deriv_nonneg c hc.1; rw [ hc.2, le_div_iff₀ ] at this <;> norm_num at * <;> linarith;
      intro b hb; rw [ h_deriv b hb ] ; specialize h_ineq b hb; nlinarith [ show 0 ≤ p * ( p - 1 ) * b by exact mul_nonneg ( mul_nonneg ( by linarith ) ( by linarith ) ) ( by linarith [ hb.1 ] ), show ( 1 + ( p - 1 ) * b ^ 2 ) ^ ( p / 2 - 1 ) ≤ 1 by exact le_trans ( Real.rpow_le_rpow_of_exponent_le ( by nlinarith [ hb.1, hb.2 ] ) ( show p / 2 - 1 ≤ 0 by linarith ) ) ( by norm_num ) ] ;
    intro b hb;
    by_cases hb0 : b = 0;
    · aesop;
    · -- Apply the Mean Value Theorem to the interval [0, b].
      obtain ⟨c, hc⟩ : ∃ c ∈ Set.Ioo 0 b, deriv f c = (f b - f 0) / (b - 0) := by
        apply_rules [ exists_deriv_eq_slope ];
        · exact lt_of_le_of_ne hb.1 ( Ne.symm hb0 );
        · exact continuousOn_of_forall_continuousAt fun x hx => by exact ContinuousAt.sub ( ContinuousAt.div ( ContinuousAt.add ( ContinuousAt.rpow ( continuousAt_const.add continuousAt_id ) continuousAt_const <| Or.inr <| by linarith ) ( ContinuousAt.rpow ( continuousAt_const.sub continuousAt_id ) continuousAt_const <| Or.inr <| by linarith ) ) continuousAt_const <| by linarith ) ( ContinuousAt.rpow ( ContinuousAt.add continuousAt_const <| ContinuousAt.mul continuousAt_const <| continuousAt_id.pow 2 ) continuousAt_const <| Or.inr <| by linarith ) ;
        · exact fun x hx => DifferentiableAt.differentiableWithinAt ( by exact DifferentiableAt.sub ( DifferentiableAt.div ( DifferentiableAt.add ( DifferentiableAt.rpow ( differentiableAt_id.const_add _ ) ( by norm_num ) ( by linarith [ hx.1 ] ) ) ( DifferentiableAt.rpow ( differentiableAt_id.const_sub _ ) ( by norm_num ) ( by linarith [ hx.2, hb.2 ] ) ) ) ( by norm_num ) ( by linarith [ hx.1, hx.2 ] ) ) ( DifferentiableAt.rpow ( by norm_num ) ( by norm_num ) ( by nlinarith [ hx.1, hx.2, hb.1, hb.2, show p - 1 ≥ 0 by linarith ] ) ) );
      norm_num +zetaDelta at *;
      have := h_f_deriv_nonneg c hc.1.1 ( by linarith ) ; rw [ hc.2, le_div_iff₀ ( by linarith ) ] at this; linarith;
  exact sub_nonneg.mp (h_f_nonneg b ⟨hb0, hb1⟩)

/-
**Two-Point Inequality** (core real inequality, a = 0 case).
For 1 ≤ p ≤ 2: (p-1)^{p/2} ≤ 1, which gives the inequality when a = 0.
-/
lemma two_point_ineq_a_zero (p : ℝ) (hp1 : 1 ≤ p) (hp2 : p ≤ 2) :
    (p - 1) ^ (p / 2) ≤ 1 := by
  exact Real.rpow_le_one ( by linarith ) ( by linarith ) ( by linarith )

/-
Noise operator doesn't increase L2 norm when we take absolute values.
For 0 ≤ ρ ≤ 1: a² + ρ²b² ≤ ((|u|+|v|)/2)² + ρ²((|u|-|v|)/2)² where u=a+b, v=a-b.
-/
lemma noise_l2_abs_mono (a b ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    a ^ 2 + ρ ^ 2 * b ^ 2 ≤
    ((|a + b| + |a - b|) / 2) ^ 2 + ρ ^ 2 * ((|a + b| - |a - b|) / 2) ^ 2 := by
  -- By simplifying, we can see that the inequality holds because the left-hand side is less than or equal to the right-hand side.
  have h_simp : (a + b) * (a - b) ≤ |a + b| * |a - b| := by
    cases abs_cases ( a + b ) <;> cases abs_cases ( a - b ) <;> nlinarith;
  nlinarith [ show 0 ≤ 1 - ρ ^ 2 by nlinarith, abs_mul_abs_self ( a + b ), abs_mul_abs_self ( a - b ) ]

/-
**Two-Point Inequality** (full version).
For 1 ≤ p ≤ 2 and all a, b ∈ ℝ, 0 ≤ ρ, ρ² ≤ p − 1:
  (a² + ρ²b²)^{1/2} ≤ ((|a+b|^p + |a−b|^p) / 2)^{1/p}
-/
theorem two_point_ineq (a b p ρ : ℝ) (hp1 : 1 ≤ p) (hp2 : p ≤ 2)
    (hρ0 : 0 ≤ ρ) (hρ : ρ ^ 2 ≤ p - 1) :
    (a ^ 2 + ρ ^ 2 * b ^ 2) ^ ((1 : ℝ) / 2) ≤
    ((|a + b| ^ p + |a - b| ^ p) / 2) ^ ((1 : ℝ) / p) := by
  -- By symmetry and homogeneity, we can assume without loss of generality that $a \geq |b|$.
  suffices h_wlog : ∀ {a b : ℝ}, 0 ≤ a → |b| ≤ a → (a ^ 2 + (p - 1) * b ^ 2) ^ (p / 2) ≤ ((a + b) ^ p + (a - b) ^ p) / 2 by
    -- Apply the suffices statement to each case.
    have h_apply_wlog : (a ^ 2 + (p - 1) * b ^ 2) ^ (p / 2) ≤ ((|a + b| ^ p + |a - b| ^ p) / 2) := by
      by_cases h_abs : |a| ≥ |b|;
      · cases le_or_gt 0 a with
        | inl ha =>
          have h_b : |b| ≤ a := by
            rw [abs_of_nonneg ha] at h_abs
            exact h_abs
          have h := h_wlog ha h_b
          have eq1 : a + b = |a + b| := (abs_of_nonneg (by have := abs_le.mp h_b; linarith)).symm
          have eq2 : a - b = |a - b| := (abs_of_nonneg (by have := abs_le.mp h_b; linarith)).symm
          rwa [eq1, eq2] at h
        | inr ha =>
          have ha_pos : 0 ≤ -a := by linarith
          have h_b : |b| ≤ -a := by
            rw [abs_of_neg ha] at h_abs
            exact h_abs
          have h := @h_wlog (-a) b ha_pos h_b
          have eq_LHS : (-a) ^ 2 = a ^ 2 := by ring
          have eq1 : -a + b = |a - b| := by
            rw [abs_of_nonpos (by have := abs_le.mp h_b; linarith)]
            ring
          have eq2 : -a - b = |a + b| := by
            rw [abs_of_nonpos (by have := abs_le.mp h_b; linarith)]
            ring
          have eq3 : |a - b| ^ p + |a + b| ^ p = |a + b| ^ p + |a - b| ^ p := add_comm (|a - b| ^ p) (|a + b| ^ p)
          rwa [eq_LHS, eq1, eq2, eq3] at h
      · -- By symmetry, we can assume without loss of generality that $|a| \geq |b|$.
        suffices h_symm : (b ^ 2 + (p - 1) * a ^ 2) ^ (p / 2) ≤ ((|b + a| ^ p + |b - a| ^ p) / 2) by
          simp_all +decide [ add_comm, abs_sub_comm ];
          refine le_trans ?_ h_symm;
          exact Real.rpow_le_rpow ( by nlinarith [ abs_lt.mp h_abs ] ) ( by nlinarith [ abs_lt.mp h_abs, show a ^ 2 ≤ b ^ 2 by nlinarith [ abs_lt.mp h_abs, abs_mul_abs_self a, abs_mul_abs_self b ] ] ) ( by positivity );
        cases abs_cases b <;> cases abs_cases a <;> simp +decide [ * ] at *;
        · convert h_wlog ‹0 ≤ b› ( show |a| ≤ b by rw [ abs_of_nonneg ] <;> linarith ) using 1 ; rw [ abs_of_nonneg ( by linarith : 0 ≤ b + a ), abs_of_nonneg ( by linarith : 0 ≤ b - a ) ];
        · convert h_wlog ‹0 ≤ b› ( show |a| ≤ b by cases abs_cases a <;> linarith ) using 1 ;
          rw [ abs_of_nonneg ( by linarith : 0 ≤ b + a ), abs_of_nonneg ( by linarith : 0 ≤ b - a ) ];
        · convert h_wlog ( show 0 ≤ -b by linarith ) ( show |a| ≤ -b by rw [ abs_of_nonneg ] <;> linarith ) using 1 <;> ring_nf;
          rw [ abs_of_nonpos, abs_of_nonpos ] <;> ring_nf <;> linarith;
        · convert h_wlog ( show 0 ≤ -b by linarith ) ( show |a| ≤ -b by cases abs_cases a <;> linarith ) using 1 <;> norm_num [ abs_of_nonpos, * ] ; ring_nf;
          rw [ abs_of_nonpos, abs_of_nonpos ] <;> ring_nf <;> linarith;
    refine' le_trans _ ( Real.rpow_le_rpow ( _ ) h_apply_wlog ( by positivity ) );
    · rw [ ← Real.rpow_mul ( by nlinarith ) ] ; ring_nf ;
      rw [ mul_inv_cancel₀ ( by linarith ), one_mul ] ; exact Real.rpow_le_rpow ( by positivity ) ( by nlinarith ) ( by positivity ) ;
    · exact Real.rpow_nonneg ( by nlinarith ) _;
  intros a b ha hb
  by_cases h : a = 0;
  · simp_all +decide [ show b = 0 by linarith [ abs_le.mp hb ] ];
    rw [ Real.zero_rpow ( by positivity ), Real.zero_rpow ( by positivity ) ];
  · -- By homogeneity, we can assume without loss of generality that $a = 1$.
    suffices h_homog : ∀ {b : ℝ}, |b| ≤ 1 → (1 + (p - 1) * b ^ 2) ^ (p / 2) ≤ ((1 + b) ^ p + (1 - b) ^ p) / 2 by
      have := @h_homog ( b / a ) ?_ <;> simp_all +decide [ abs_div, div_le_iff₀];
      · field_simp at this;
        rw [ Real.div_rpow ( by nlinarith [ abs_le.mp hb ] ) ( by positivity ), Real.div_rpow ( by nlinarith [ abs_le.mp hb ] ) ( by positivity ), Real.div_rpow ( by nlinarith [ abs_le.mp hb ] ) ( by positivity ) ] at this;
        rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ) ] at * ; ring_nf at * ; norm_num at *;
        nlinarith [ inv_pos.mpr ( Real.rpow_pos_of_pos ( lt_of_le_of_ne ha ( Ne.symm h ) ) p ) ];
      · rwa [ abs_of_nonneg ha ];
    intros b hb
    by_cases h : b ≥ 0;
    · have := @two_point_ineq_unit b p hp1 hp2 h ( by linarith [ abs_le.mp hb ] ) ; aesop;
    · have := two_point_ineq_unit ( -b ) p hp1 hp2 ( by linarith [ abs_le.mp hb ] ) ( by linarith [ abs_le.mp hb ] ) ; ring_nf at *; aesop;

/-! ## Main theorem -/

set_option maxHeartbeats 4000000 in
/--
**One-Bit (p, 2)-Hypercontractivity Theorem**.

For f : BoolCube 1 → ℝ, 1 ≤ p ≤ 2, and 0 ≤ ρ with ρ² ≤ p − 1:
  (𝔼[(T_ρ f)²])^{1/2} ≤ (𝔼[|f|^p])^{1/p}
-/
theorem one_bit_p2_hypercontractivity (p : ℝ) (hp1 : 1 ≤ p) (hp2 : p ≤ 2)
    (ρ : ℝ) (hρ_nn : 0 ≤ ρ) (hρ : ρ ^ 2 ≤ p - 1)
    (f : BooleanFunc 1) :
    (BooleanAnalysis.expect (fun x => (noiseOp ρ f x) ^ 2)) ^ ((1 : ℝ) / 2) ≤
    (BooleanAnalysis.expect (fun x => |f x| ^ p)) ^ ((1 : ℝ) / p) := by
  set a := fourierCoeff f ∅
  set b := fourierCoeff f {⟨0, by omega⟩}
  have h1 : BooleanAnalysis.expect (fun x => (noiseOp ρ f x) ^ 2) = a ^ 2 + ρ ^ 2 * b ^ 2 :=
    expect_noiseOp_sq_one_bit ρ f
  have h2 : BooleanAnalysis.expect (fun x => |f x| ^ p) =
    (|a + b| ^ p + |a - b| ^ p) / 2 := expect_abs_rpow_one_bit p f
  rw [h1, h2]
  exact two_point_ineq a b p ρ hp1 hp2 hρ_nn hρ

/-! ## Hölder sharpness and noise operator duality -/

/-- Helper: sign(x) * x = |x| -/
private lemma sign_mul_self (x : ℝ) : Real.sign x * x = |x| := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [Real.sign_of_neg hx, abs_of_neg hx]; ring
  · simp [Real.sign_zero]
  · rw [Real.sign_of_pos hx, abs_of_pos hx, one_mul]

/-- Helper: |sign(x)| = 1 when x ≠ 0 -/
private lemma abs_sign_eq_one (x : ℝ) (hx : x ≠ 0) : |Real.sign x| = 1 := by
  rcases lt_or_gt_of_ne hx with h | h
  · simp [Real.sign_of_neg h]
  · simp [Real.sign_of_pos h]

/-- Helper: expect of pointwise nonneg function is nonneg -/
private lemma expect_nonneg_of_nonneg {n : ℕ} {f : BooleanFunc n} (hf : ∀ x, 0 ≤ f x) :
    0 ≤ expect f := by
  unfold expect uniformWeight
  exact mul_nonneg (pow_nonneg (by positivity) _) (Finset.sum_nonneg (fun x _ => hf x))

/-- Helper: expect of constant function -/
private lemma expect_const_eq {n : ℕ} (c : ℝ) :
    expect (fun (_ : BoolCube n) => c) = c := by
  unfold expect uniformWeight
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_bool, Fintype.card_fin]

/-
Helper: Cauchy-Schwarz for the Boolean inner product
-/
private lemma cauchy_schwarz_bool {n : ℕ} (f g : BooleanFunc n) :
    innerProduct f g ≤
    (expect (fun x => f x ^ 2)) ^ ((1:ℝ)/2) * (expect (fun x => g x ^ 2)) ^ ((1:ℝ)/2) := by
  norm_num [ ← Real.sqrt_eq_rpow ];
  unfold BooleanAnalysis.innerProduct BooleanAnalysis.expect;
  rw [ ← Real.sqrt_mul ];
  · refine Real.le_sqrt_of_sq_le ?_;
    -- Apply the Cauchy-Schwarz inequality to the sums.
    have h_cauchy_schwarz : (∑ x : BoolCube n, f x * g x) ^ 2 ≤ (∑ x : BoolCube n, f x ^ 2) * (∑ x : BoolCube n, g x ^ 2) :=
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g;
    convert mul_le_mul_of_nonneg_left h_cauchy_schwarz ( sq_nonneg ( uniformWeight n ) ) using 1 <;> ring;
  · exact mul_nonneg ( by exact pow_nonneg ( by norm_num ) _ ) ( Finset.sum_nonneg fun _ _ => sq_nonneg _ )

/-
**Hölder sharpness**: For Hölder conjugate exponents (p, q), for any function u,
there exists f with ‖f‖_p ≤ 1 and ‖u‖_q ≤ ⟨f, u⟩.
-/
lemma holder_sharpness {n : ℕ} {p q : ℝ}
    (hpq : Real.HolderConjugate p q)
    (u : BooleanFunc n) :
    ∃ f : BooleanFunc n,
    (expect (fun x => |f x| ^ p)) ^ (1 / p) ≤ 1 ∧
    (expect (fun x => |u x| ^ q)) ^ (1 / q) ≤ innerProduct f u := by
  refine' ⟨ fun x => Real.sign ( u x ) * ( |u x| ^ ( q - 1 ) ) / ( ( expect fun x => |u x| ^ q ) ^ ( 1 / p ) ), _, _ ⟩ <;> norm_num [ hpq.ne_zero, hpq.symm.ne_zero ];
  · by_cases h : ( expect fun x => |u x| ^ q ) ^ p⁻¹ = 0 <;> simp_all +decide [ abs_div, abs_mul, abs_of_nonneg, Real.rpow_nonneg];
    · norm_num [ hpq.ne_zero, expect_const_eq ];
    · -- Simplify the expression inside the expectation.
      have h_simp : ∀ x, (|(u x).sign| * |u x| ^ (q - 1) / |(expect fun x => |u x| ^ q) ^ p⁻¹|) ^ p = |u x| ^ q / |(expect fun x => |u x| ^ q) ^ p⁻¹| ^ p := by
        intro x; rw [ Real.div_rpow ( by positivity ) ( by positivity ), Real.mul_rpow ( by positivity ) ( by positivity ) ] ; by_cases hx : u x = 0 <;> simp_all +decide [ Real.sign ] ;
        · norm_num [ hpq.ne_zero, hpq.symm.ne_zero ];
        · split_ifs <;> simp_all +decide [ abs_of_neg, abs_of_pos ];
          · rw [ ← Real.rpow_mul ( by linarith ), mul_comm ];
            rw [ show p * ( q - 1 ) = q by linarith [ hpq.symm.sub_one_mul_conj ] ];
          · rw [ ← Real.rpow_mul ( by positivity ), mul_comm ] ; ring_nf;
            rw [ show -p + p * q = q by nlinarith [ hpq.symm.sub_one_mul_conj ] ] ; ring;
          · exact False.elim <| hx <| by linarith;
      simp_all +decide [ expect];
      simp_all +decide [ ← Finset.sum_div _ _ _ ];
      rw [ mul_div, Real.div_rpow ];
      · rw [ ← Real.rpow_mul ( abs_nonneg _ ), mul_inv_cancel₀ ( ne_of_gt hpq.pos ), Real.rpow_one, abs_of_nonneg ( Real.rpow_nonneg ( mul_nonneg ( by exact pow_nonneg ( by norm_num ) _ ) ( Finset.sum_nonneg fun _ _ => Real.rpow_nonneg ( abs_nonneg _ ) _ ) ) _ ), div_self h ];
      · exact mul_nonneg ( by exact pow_nonneg ( by norm_num ) _ ) ( Finset.sum_nonneg fun _ _ => Real.rpow_nonneg ( abs_nonneg _ ) _ );
      · positivity;
  · by_cases h : expect ( fun x => |u x| ^ q ) = 0 <;> simp_all +decide [ div_eq_mul_inv, mul_assoc, mul_comm, hpq.ne_zero, hpq.symm.ne_zero ];
    · unfold innerProduct;
      unfold expect; norm_num;
    · -- Simplify the expression using the properties of exponents and absolute values.
      have h_simp : expect (fun x => |u x| ^ (q - 1) * (Real.sign (u x)) * ((expect (fun x => |u x| ^ q)) ^ p⁻¹)⁻¹ * u x) = (expect (fun x => |u x| ^ q)) / ((expect (fun x => |u x| ^ q)) ^ p⁻¹) := by
        have h_simp : ∀ x, |u x| ^ (q - 1) * (Real.sign (u x)) * u x = |u x| ^ q := by
          intro x; rw [ Real.sign ] ; split_ifs <;> ring_nf;
          · rw [ abs_of_neg ‹_› ] ; ring_nf;
            rw [ show q = -1 + q + 1 by ring, Real.rpow_add_one ] <;> ring_nf ; linarith;
          · rw [ abs_of_pos ‹_›, ← Real.rpow_add_one ] <;> ring_nf ; linarith;
          · norm_num [ show u x = 0 by linarith, hpq.symm.ne_zero ]
        generalize_proofs at *; (
        simp +decide only [mul_right_comm, h_simp, div_eq_mul_inv];
        unfold expect; norm_num [ Finset.sum_mul _ _ _ ] ;
        rw [ ← Finset.sum_mul _ _ _, mul_assoc ])
      generalize_proofs at *; (
      -- Using the properties of exponents, we can simplify the right-hand side.
      have h_exp : (expect (fun x => |u x| ^ q)) / ((expect (fun x => |u x| ^ q)) ^ p⁻¹) = (expect (fun x => |u x| ^ q)) ^ (1 - p⁻¹) := by
        rw [ Real.rpow_sub ( lt_of_le_of_ne ( by exact expect_nonneg_of_nonneg fun x => by positivity ) ( Ne.symm h ) ), Real.rpow_one ]
      generalize_proofs at *; (
      simp_all +decide [ mul_assoc, mul_comm, innerProduct ];
      rw [ show q⁻¹ = 1 - p⁻¹ by linarith [ hpq.symm.inv_add_inv_eq_one ] ]))

/-
**Noise operator duality**: (p, 2)-hypercontractivity implies (p', 2)-hypercontractivity
in the reverse direction, where p' is the Hölder conjugate of p.
-/
theorem noise_operator_duality
  {p p_conj : ℝ}
  (hp_conj : Real.HolderConjugate p p_conj)
  (h_p1 : 1 ≤ p)
  (h_hyp : ∀ f : BooleanFunc 1,
    (expect (fun x => |noiseOp (Real.sqrt (p - 1)) f x| ^ (2 : ℝ))) ^ (1 / 2 : ℝ) ≤
    (expect (fun x => |f x| ^ p)) ^ (1 / p)) :
  ∀ g : BooleanFunc 1,
    (expect (fun x => |noiseOp (Real.sqrt (p - 1)) g x| ^ p_conj)) ^ (1 / p_conj) ≤
    (expect (fun x => |g x| ^ (2 : ℝ))) ^ (1 / 2 : ℝ) := by
  intro g
  obtain ⟨f, hf⟩ := holder_sharpness hp_conj (noiseOp (Real.sqrt (p - 1)) g);
  refine hf.2.trans ?_;
  have := @cauchy_schwarz_bool 1 ( noiseOp ( Real.sqrt ( p - 1 ) ) f ) g;
  refine' le_trans _ ( this.trans _ );
  · rw [ noiseOp_self_adjoint ];
  · refine' le_trans ( mul_le_of_le_one_left ( Real.rpow_nonneg ( _ ) _ ) _ ) _;
    · exact expect_sq_nonneg g;
    · convert h_hyp f |> le_trans <| hf.1 using 1;
      norm_num [ sq_abs ];
    · norm_num [ sq_abs ]

/--
**One-Bit (2, q)-Hypercontractivity Theorem**.
For g : BoolCube 1 → ℝ and q ≥ 2:
  ‖T_{1 / √(q - 1)} g‖_q ≤ ‖g‖_2
-/
theorem one_bit_2q_hypercontractivity (q : ℝ) (hq2 : 2 ≤ q) (g : BooleanFunc 1) :
    (expect (fun x => |noiseOp (1 / Real.sqrt (q - 1)) g x| ^ q)) ^ (1 / q) ≤
    (expect (fun x => |g x| ^ (2 : ℝ))) ^ (1 / 2 : ℝ) := by
  -- Define p as the Hölder conjugate of q
  set p := q / (q - 1)
  have hq_sub_one_pos : 0 < q - 1 := by linarith

  -- Verify the bounds 1 ≤ p ≤ 2
  have hp1 : 1 ≤ p := by
    dsimp [p]
    rw [le_div_iff₀ hq_sub_one_pos]
    linarith

  have hp2 : p ≤ 2 := by
    dsimp [p]
    rw [div_le_iff₀ hq_sub_one_pos]
    linarith

  -- Prove that p and q are Hölder conjugates
  have hpq : Real.HolderConjugate p q := by
    constructor
    · dsimp [p]
      have : q ≠ 0 := by linarith
      have : q - 1 ≠ 0 := by linarith
      field_simp
      ring_nf
    · dsimp [p]
      rw [lt_div_iff₀ hq_sub_one_pos]
      linarith
    · linarith

  -- Relate the noise parameter from p back to q
  have h_sqrt : Real.sqrt (p - 1) = 1 / Real.sqrt (q - 1) := by
    have h_sub : p - 1 = 1 / (q - 1) := by
      dsimp [p]
      have : q - 1 ≠ 0 := by linarith
      field_simp
      ring
    rw [h_sub, Real.sqrt_div, Real.sqrt_one]
    linarith

  -- Show that the premise holds via the (p, 2) hypercontractivity theorem
  have h_hyp : ∀ f : BooleanFunc 1,
      (expect (fun x => |noiseOp (Real.sqrt (p - 1)) f x| ^ (2 : ℝ))) ^ (1 / 2 : ℝ) ≤
      (expect (fun x => |f x| ^ p)) ^ (1 / p) := by
    intro f
    have h_p2_hyp := one_bit_p2_hypercontractivity p hp1 hp2
      (Real.sqrt (p - 1))
      (Real.sqrt_nonneg _)
      (by rw [Real.sq_sqrt (by linarith)]) f

    -- Helper lemma to convert |y|^(2:ℝ) to y^2
    have h_pow : ∀ y : ℝ, |y| ^ (2 : ℝ) = y ^ 2 := by
      intro y
      rw [Real.rpow_two, sq_abs]

    -- simp_rw dives into the `expect` binder and seamlessly rewrites the power
    simp_rw [h_pow]
    exact h_p2_hyp

  -- Finally, apply the duality theorem and substitute the noise parameter
  have h_dual := noise_operator_duality hpq hp1 h_hyp g
  rwa [h_sqrt] at h_dual

section
open BooleanAnalysis Real Bonami Hypercontractivity

variable {n : ℕ}

/-! ## Noise Kernel -/

/-- The noise kernel `K_ρ(x, y) = ∏_i (1 + ρ · sign(x_i) · sign(y_i)) / 2`.
This is the transition probability from `x` to `y` under ρ-correlated noise. -/
noncomputable def noiseKernel (ρ : ℝ) {n : ℕ} (x y : BoolCube n) : ℝ :=
  ∏ i : Fin n, (1 + ρ * boolToSign (x i) * boolToSign (y i)) / 2

lemma noiseKernel_nonneg {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (x y : BoolCube n) : 0 ≤ noiseKernel ρ x y := by
  refine Finset.prod_nonneg fun i _ ↦ ?_
  cases x i <;> cases y i <;> norm_num [boolToSign] <;> nlinarith
/-! ## Noise Operator as Kernel Sum -/

lemma sum_fourier_kernel (ρ : ℝ) (x y : BoolCube n) :
    ∑ S : Finset (Fin n), ρ ^ S.card * chiS S x * chiS S y =
    ∏ i : Fin n, (1 + ρ * boolToSign (x i) * boolToSign (y i)) := by
  have h_prod_sum : ∏ i : Fin n, (1 + ρ * boolToSign (x i) * boolToSign (y i)) =
      ∑ S : Finset (Fin n), ∏ i ∈ S, (ρ * boolToSign (x i) * boolToSign (y i)) := by
    simp +decide [add_comm, Finset.prod_add]
  rw [h_prod_sum, Finset.sum_congr rfl]
  intros; simp_all +decide [Finset.prod_mul_distrib, chiS]

/-- The noise operator equals a kernel sum: `T_ρ g(x) = ∑_y K_ρ(x,y) · g(y)`. -/
lemma noiseOp_eq_kernel_sum (ρ : ℝ) (g : BooleanFunc n) (x : BoolCube n) :
    noiseOp ρ g x = ∑ y : BoolCube n, noiseKernel ρ x y * g y := by
  unfold noiseOp noiseKernel BooleanAnalysis.fourierCoeff BooleanAnalysis.innerProduct
  simp +decide [BooleanAnalysis.expect]
  unfold uniformWeight
  simp +decide [div_eq_inv_mul, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]
  rw [Finset.sum_comm, Finset.sum_congr rfl]; intros; ring_nf
  rw [← sum_fourier_kernel]
  simp +decide [mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum]

/-! ## Inner Product as Kernel-Weighted Sum -/

/-- `⟨f, T_ρ g⟩ = (1/2^n) ∑_{x,y} K_ρ(x,y) · f(x) · g(y)`. -/
lemma innerProduct_noiseOp_eq_weighted_sum (ρ : ℝ) (f g : BooleanFunc n) :
    innerProduct f (noiseOp ρ g) =
    uniformWeight n * ∑ x : BoolCube n, ∑ y : BoolCube n,
      noiseKernel ρ x y * f x * g y := by
  unfold innerProduct
  simp +decide [mul_assoc, Finset.mul_sum, expect]
  rw [Finset.sum_congr rfl fun _ _ => ?_]
  rw [noiseOp_eq_kernel_sum]
  simp +decide [mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum]

/-! ## Correlated Monotonicity -/

/-- If `h(x,y) ≤ h'(x,y)` pointwise and `0 ≤ ρ ≤ 1`, then the kernel-weighted
expectation of `h` is at most that of `h'`. -/
lemma corrExpect_mono {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    {h h' : BoolCube n → BoolCube n → ℝ} (hle : ∀ x y, h x y ≤ h' x y) :
    uniformWeight n * ∑ x : BoolCube n, ∑ y : BoolCube n,
      noiseKernel ρ x y * h x y ≤
    uniformWeight n * ∑ x : BoolCube n, ∑ y : BoolCube n,
      noiseKernel ρ x y * h' x y := by
  apply_rules [mul_le_mul_of_nonneg_left, Finset.sum_le_sum]
  · exact fun x _ => Finset.sum_le_sum fun y _ =>
      mul_le_mul_of_nonneg_left (hle x y) (noiseKernel_nonneg hρ0 hρ1 x y)
  · exact pow_nonneg (by norm_num) _

/-! ## Noise Kernel Factorization -/

/-- The noise kernel on `BoolCube (n+1)` factors along the last coordinate. -/
lemma noiseKernel_snoc (ρ : ℝ) (x' y' : BoolCube n) (b b' : Bool) :
    noiseKernel ρ (Fin.snoc x' b) (Fin.snoc y' b') =
    noiseKernel ρ x' y' * ((1 + ρ * boolToSign b * boolToSign b') / 2) := by
  unfold noiseKernel; simp +decide [Fin.prod_univ_castSucc]; ring

/-! ## Expectation Decomposition (Fubini for BoolCube) -/

lemma expect_succ_eq_iterated (h : BooleanFunc (n + 1)) :
    expect h = expect (fun x' =>
      (1/2 : ℝ) * (h (Fin.snoc x' false) + h (Fin.snoc x' true))) := by
  unfold expect
  rw [sum_boolCube_succ]
  norm_num [Finset.mul_sum, mul_add, mul_assoc, mul_left_comm,
            Finset.sum_add_distrib, uniformWeight_succ]
  ring_nf

/-! ## Norm Collapse (Fubini) -/

lemma norm_collapse_rpow (p : ℝ) (hp : 0 < p) (f : BooleanFunc (n + 1)) :
    expect (fun x => |f x| ^ p) =
    expect (fun x' => (1/2 : ℝ) *
      (|f (Fin.snoc x' false)| ^ p + |f (Fin.snoc x' true)| ^ p)) := by
  convert expect_succ_eq_iterated _ using 1

/-! ## Decomposition of Weighted Sum at Dimension n+1 -/

/-
The kernel-weighted bilinear sum at dimension `n+1` decomposes by factoring the
kernel along the last coordinate.
-/
lemma weighted_sum_succ_decomp (ρ : ℝ) (F : BoolCube (n + 1) → BoolCube (n + 1) → ℝ) :
    uniformWeight (n + 1) * ∑ x : BoolCube (n + 1), ∑ y : BoolCube (n + 1),
      noiseKernel ρ x y * F x y =
    uniformWeight n * ∑ x' : BoolCube n, ∑ y' : BoolCube n,
      noiseKernel ρ x' y' *
      ((1/2 : ℝ) * ∑ b : Bool, ∑ b' : Bool,
        ((1 + ρ * boolToSign b * boolToSign b') / 2) *
        F (Fin.snoc x' b) (Fin.snoc y' b')) := by
  convert congr_arg _ ( sum_boolCube_succ fun y => ∑ x, noiseKernel ρ y x * F y x ) using 1 ; norm_num ; ring_nf!;
  rw [ add_comm 1, uniformWeight_succ ] ; simp +decide [ Finset.sum_add_distrib, mul_assoc, mul_left_comm, mul_add, Finset.sum_add_distrib, mul_assoc, mul_left_comm,
    mul_add, Finset.sum_add_distrib, mul_assoc, mul_left_comm, mul_add, Finset.sum_add_distrib, Finset.mul_sum _ _ _, mul_assoc, mul_left_comm, mul_add] ; ring_nf;
  simp +decide only [← Finset.sum_add_distrib] ; ring_nf;
  refine' Finset.sum_congr rfl fun x _ => _ ; rw [ sum_boolCube_succ ] ; ring_nf;
  rw [ ← Finset.sum_add_distrib ] ; congr ; ext y ; rw [ noiseKernel_snoc, noiseKernel_snoc ] ; ring_nf;
  rw [ noiseKernel_snoc, noiseKernel_snoc ] ; norm_num [ boolToSign ] ; ring;

/-! ## One-Bit Correlated Expectation as Inner Product -/

/-
For fixed `x'` and `y'`, the one-bit kernel-weighted sum of the slices of `f` and `g`
equals the one-bit inner product with noise operator.
-/
lemma one_bit_slice_eq_innerProduct (ρ : ℝ) (f g : BooleanFunc (n + 1))
    (x' y' : BoolCube n) :
    (1/2 : ℝ) * ∑ b : Bool, ∑ b' : Bool,
      ((1 + ρ * boolToSign b * boolToSign b') / 2) *
      f (Fin.snoc x' b) * g (Fin.snoc y' b') =
    innerProduct (fun t : BoolCube 1 => f (Fin.snoc x' (t 0)))
                 (noiseOp ρ (fun t : BoolCube 1 => g (Fin.snoc y' (t 0)))) := by
  unfold BooleanAnalysis.noiseOp;
  unfold BooleanAnalysis.innerProduct BooleanAnalysis.fourierCoeff
  simp;
  rw [ show ( Finset.univ : Finset ( Finset ( Fin 1 ) ) ) = { ∅, { 0 } } by decide ] ; norm_num ; ring_nf;
  unfold BooleanAnalysis.expect; norm_num [ Finset.sum_range_succ, Finset.sum_range_zero, BooleanAnalysis.innerProduct ] ; ring_nf;
  unfold BooleanAnalysis.expect; norm_num [ Finset.sum_range_succ, Finset.sum_range_zero, BooleanAnalysis.uniformWeight ] ; ring_nf;
  rw [ show ( Finset.univ : Finset ( BoolCube 1 ) ) = { fun _ => false, fun _ => true } by decide ] ; norm_num ; ring_nf;
  rw [ Finset.sum_pair, Finset.sum_pair ] <;> norm_num [ boolToSign ] ; ring_nf;
  · grind +splitImp;
  · exact fun h => by have := congr_fun h 0; simp +decide at this;
  · exact fun h => by have := congr_fun h 0; simp +decide at this;

/-! ## One-bit Lp norm of slices -/

/-
The one-bit `L^p` norm of the slice `t ↦ f(snoc x' (t 0))`.
-/
lemma one_bit_norm_slice (p : ℝ) (hp : 0 < p) (f : BooleanFunc (n + 1)) (x' : BoolCube n) :
    (expect (fun t : BoolCube 1 => |f (Fin.snoc x' (t 0))| ^ p)) ^ (1/p) =
    ((|f (Fin.snoc x' false)| ^ p + |f (Fin.snoc x' true)| ^ p) / 2) ^ (1/p) := by
  unfold expect;
  unfold uniformWeight; norm_num [ Finset.card_univ ] ; ring_nf;
  rw [ show ( Finset.univ : Finset ( Fin 1 → Bool ) ) = { fun _ => Bool.false, fun _ => Bool.true } by decide, Finset.sum_pair ] <;> norm_num ; ring_nf;
  decide +revert

/-! ## Norm Collapse (clean form) -/

/-
The iterated norm collapses: `E_{x'}[F(x')^p] = E_x[|f(x)|^p]` where
`F(x') = (E_t[|f(x',t)|^p])^{1/p}`.
-/
lemma norm_collapse_clean (p : ℝ) (hp : 1 ≤ p) (f : BooleanFunc (n + 1)) :
    expect (fun x' =>
      ((|f (Fin.snoc x' false)| ^ p + |f (Fin.snoc x' true)| ^ p) / 2) ) =
    expect (fun x => |f x| ^ p) := by
  convert norm_collapse_rpow p ( by linarith ) f |> Eq.symm using 2;
  exact funext fun x' => by ring;

/-! ## Main Theorem: Two-Function Hypercontractivity by Induction -/

/-
Helper: the zero-dimensional case is trivial.
-/
lemma two_func_hyp_zero
    (p q : ℝ) (hp : 1 ≤ p) (hq : 1 ≤ q) (ρ : ℝ)
    (f g : BooleanFunc 0) :
    innerProduct f (noiseOp ρ g) ≤
    (expect (fun x => |f x| ^ p)) ^ (1/p) *
    (expect (fun x => |g x| ^ q)) ^ (1/q) := by
  unfold innerProduct BooleanAnalysis.expect;
  unfold uniformWeight;
  -- By definition of noiseOp, we have noiseOp ρ g x = g x for any x.
  have h_noiseOp : ∀ x, noiseOp ρ g x = g x := by
    intro x;
    unfold noiseOp;
    rw [ show ( Finset.univ : Finset ( Finset ( Fin 0 ) ) ) = { ∅ } by decide, Finset.sum_singleton ] ; norm_num [ BooleanAnalysis.fourierCoeff, BooleanAnalysis.chiS ];
    unfold innerProduct; norm_num [ BooleanAnalysis.expect ] ;
    unfold uniformWeight; norm_num;
    exact congr_arg g ( Subsingleton.elim _ _ );
  simp_all +decide [ show ∀ x : Fin 0 → Bool, x = fun _ => Bool.true by intro x; ext i; exact Fin.elim0 i ];
  rw [ ← Real.rpow_mul ( abs_nonneg _ ), ← Real.rpow_mul ( abs_nonneg _ ), mul_inv_cancel₀ ( by positivity ), mul_inv_cancel₀ ( by positivity ), Real.rpow_one, Real.rpow_one ];
  cases abs_cases ( f fun _ => true ) <;> cases abs_cases ( g fun _ => true ) <;> nlinarith

/-
Helper: the inductive step. Given the result for dimension n,
prove it for dimension n+1 using the one-bit base case.
-/
lemma two_func_hyp_succ
    (p q : ℝ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (base_case : ∀ (f g : BooleanFunc 1),
      innerProduct f (noiseOp ρ g) ≤
      (expect (fun x => |f x| ^ p)) ^ (1/p) *
      (expect (fun x => |g x| ^ q)) ^ (1/q))
    (ih : ∀ (f g : BooleanFunc n),
      innerProduct f (noiseOp ρ g) ≤
      (expect (fun x => |f x| ^ p)) ^ (1/p) *
      (expect (fun x => |g x| ^ q)) ^ (1/q))
    (f g : BooleanFunc (n + 1)) :
    innerProduct f (noiseOp ρ g) ≤
    (expect (fun x => |f x| ^ p)) ^ (1/p) *
    (expect (fun x => |g x| ^ q)) ^ (1/q) := by
  nontriviality;
  revert f g;
  intro f g;
  -- Apply the one-bit slice decomposition to rewrite the left-hand side.
  have h_lhs : ⟪f, noiseOp ρ g⟫_𝔹 = uniformWeight n * ∑ x' : BoolCube n, ∑ y' : BoolCube n, noiseKernel ρ x' y' * ⟪fun t : BoolCube 1 => f (Fin.snoc x' (t 0)), noiseOp ρ (fun t : BoolCube 1 => g (Fin.snoc y' (t 0)))⟫_𝔹 := by
    have h_lhs : ⟪f, noiseOp ρ g⟫_𝔹 = uniformWeight (n + 1) * ∑ x : BoolCube (n + 1), ∑ y : BoolCube (n + 1), noiseKernel ρ x y * f x * g y := by
      convert innerProduct_noiseOp_eq_weighted_sum ρ f g using 1;
    convert weighted_sum_succ_decomp ρ ( fun x y => f x * g y ) using 1;
    · simpa only [ mul_assoc ] using h_lhs;
    · congr! 3;
      exact congrArg _ ( one_bit_slice_eq_innerProduct ρ f g _ _ ▸ by ac_rfl );
  -- Apply the pointwise bound from `base_case` to each term in the sum.
  have h_pointwise : ∀ x' y' : BoolCube n, ⟪fun t : BoolCube 1 => f (Fin.snoc x' (t 0)), noiseOp ρ (fun t : BoolCube 1 => g (Fin.snoc y' (t 0)))⟫_𝔹 ≤
    ((|f (Fin.snoc x' false)| ^ p + |f (Fin.snoc x' true)| ^ p) / 2) ^ (1 / p) *
    ((|g (Fin.snoc y' false)| ^ q + |g (Fin.snoc y' true)| ^ q) / 2) ^ (1 / q) := by
      intro x' y';
      convert base_case _ _ using 1;
      unfold expect;
      unfold uniformWeight;
      erw [ show ( Finset.univ : Finset ( Fin 1 → Bool ) ) = { fun _ => Bool.false, fun _ => Bool.true } by decide ] ; simp +decide ; ring_nf;
  -- Apply the pointwise bound from `h_pointwise` to each term in the sum.
  have h_sum_bound : ⟪f, noiseOp ρ g⟫_𝔹 ≤ uniformWeight n * ∑ x' : BoolCube n, ∑ y' : BoolCube n, noiseKernel ρ x' y' *
    ((|f (Fin.snoc x' false)| ^ p + |f (Fin.snoc x' true)| ^ p) / 2) ^ (1 / p) *
    ((|g (Fin.snoc y' false)| ^ q + |g (Fin.snoc y' true)| ^ q) / 2) ^ (1 / q) := by
      rw [h_lhs];
      exact mul_le_mul_of_nonneg_left ( Finset.sum_le_sum fun x' _ => Finset.sum_le_sum fun y' _ => by simpa only [ mul_assoc ] using mul_le_mul_of_nonneg_left ( h_pointwise x' y' ) ( noiseKernel_nonneg hρ0 hρ1 x' y' ) ) ( by exact pow_nonneg ( by norm_num ) _ );
  -- Apply the induction hypothesis to bound the sum.
  have h_ind_bound : ⟪(fun x' => ((|f (Fin.snoc x' false)| ^ p + |f (Fin.snoc x' true)| ^ p) / 2) ^ (1 / p)), noiseOp ρ (fun y' => ((|g (Fin.snoc y' false)| ^ q + |g (Fin.snoc y' true)| ^ q) / 2) ^ (1 / q))⟫_𝔹 ≤
    (expect (fun x' => ((|f (Fin.snoc x' false)| ^ p + |f (Fin.snoc x' true)| ^ p) / 2))) ^ (1 / p) *
    (expect (fun y' => ((|g (Fin.snoc y' false)| ^ q + |g (Fin.snoc y' true)| ^ q) / 2))) ^ (1 / q) := by
      convert ih _ _ using 3 <;> norm_num [ abs_of_nonneg, Real.rpow_nonneg, add_nonneg, div_nonneg, Real.rpow_nonneg, abs_nonneg ];
      · exact congr_arg _ ( funext fun x => by rw [ ← Real.rpow_mul ( by positivity ), inv_mul_cancel₀ ( by positivity ), Real.rpow_one ] );
      · exact congr_arg _ ( funext fun x => by rw [ ← Real.rpow_mul ( by positivity ), inv_mul_cancel₀ ( by positivity ), Real.rpow_one ] );
  refine le_trans h_sum_bound ?_;
  convert h_ind_bound using 1;
  · rw [ innerProduct_noiseOp_eq_weighted_sum ];
  · congr! 2;
    · convert norm_collapse_clean p hp f |> Eq.symm using 1;
    · convert norm_collapse_clean q ( by linarith ) g |> Eq.symm using 1

theorem hypercontractivity_induction
    (p q : ℝ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (base_case : ∀ (f g : BooleanFunc 1),
      innerProduct f (noiseOp ρ g) ≤
      (expect (fun x => |f x| ^ p)) ^ (1/p) *
      (expect (fun x => |g x| ^ q)) ^ (1/q))
    {n : ℕ} (f g : BooleanFunc n) :
    innerProduct f (noiseOp ρ g) ≤
    (expect (fun x => |f x| ^ p)) ^ (1/p) *
    (expect (fun x => |g x| ^ q)) ^ (1/q) := by
  induction n with
  | zero => exact two_func_hyp_zero p q hp hq ρ f g
  | succ n ih =>
    exact two_func_hyp_succ p q hp hq ρ hρ0 hρ1 base_case
      (fun f' g' => ih f' g') f g

/--
**Weak Two-Function Hypercontractivity on a Single Bit.**
For f, g : BoolCube 1 → ℝ, and exponents 1 ≤ p ≤ 2, 1 ≤ q ≤ 2, setting
ρ = √((p − 1)(q − 1)):
  ⟨f, T_ρ g⟩ ≤ (𝔼[|f|^p])^{1/p} · (𝔼[|g|^q])^{1/q}
The proof factorizes ρ = √(p−1) · √(q−1), uses the semigroup property and
self-adjointness of T, applies Cauchy–Schwarz, and then bounds each L² norm
via one-bit (p, 2)-hypercontractivity.
-/
theorem weak_two_function_hypercontractivity_one_bit
    (p q : ℝ) (hp1 : 1 ≤ p) (hp2 : p ≤ 2) (hq1 : 1 ≤ q) (hq2 : q ≤ 2)
    (f g : BooleanFunc 1) :
    innerProduct f (noiseOp (Real.sqrt ((p - 1) * (q - 1))) g) ≤
    (expect (fun x => |f x| ^ p)) ^ (1 / p) *
    (expect (fun x => |g x| ^ q)) ^ (1 / q) := by
  -- Step 1: Factor the noise parameter √((p-1)(q-1)) = √(p-1) · √(q-1)
  have hp_sub : 0 ≤ p - 1 := by linarith
  have hq_sub : 0 ≤ q - 1 := by linarith
  have h_sqrt_factor : Real.sqrt ((p - 1) * (q - 1)) = Real.sqrt (p - 1) * Real.sqrt (q - 1) := by
    exact Real.sqrt_mul hp_sub (q - 1)
  -- Step 2: Rewrite using semigroup property T_{ab} = T_a ∘ T_b
  have h_compose : noiseOp (Real.sqrt ((p - 1) * (q - 1))) g =
      noiseOp (Real.sqrt (p - 1)) (noiseOp (Real.sqrt (q - 1)) g) := by
    rw [h_sqrt_factor, ← noiseOp_compose]
  rw [h_compose]
  -- Step 3: Use self-adjointness: ⟨f, T_{√(p-1)} h⟩ = ⟨T_{√(p-1)} f, h⟩
  rw [← noiseOp_self_adjoint]
  -- Step 4: Apply Cauchy-Schwarz
  have h_cs := cauchy_schwarz_bool (noiseOp (Real.sqrt (p - 1)) f) (noiseOp (Real.sqrt (q - 1)) g)
  -- Step 5: Apply one-bit (p,2)-hypercontractivity to each factor
  have h_hyp_f : (expect (fun x => (noiseOp (Real.sqrt (p - 1)) f x) ^ 2)) ^ ((1 : ℝ) / 2) ≤
      (expect (fun x => |f x| ^ p)) ^ (1 / p) := by
    exact one_bit_p2_hypercontractivity p hp1 hp2 (Real.sqrt (p - 1))
      (Real.sqrt_nonneg _)
      (by rw [Real.sq_sqrt hp_sub])
      f
  have h_hyp_g : (expect (fun x => (noiseOp (Real.sqrt (q - 1)) g x) ^ 2)) ^ ((1 : ℝ) / 2) ≤
      (expect (fun x => |g x| ^ q)) ^ (1 / q) := by
    exact one_bit_p2_hypercontractivity q hq1 hq2 (Real.sqrt (q - 1))
      (Real.sqrt_nonneg _)
      (by rw [Real.sq_sqrt hq_sub])
      g
  -- Chain the inequalities
  calc innerProduct (noiseOp (Real.sqrt (p - 1)) f) (noiseOp (Real.sqrt (q - 1)) g)
      ≤ (expect (fun x => (noiseOp (Real.sqrt (p - 1)) f x) ^ 2)) ^ ((1 : ℝ) / 2) *
        (expect (fun x => (noiseOp (Real.sqrt (q - 1)) g x) ^ 2)) ^ ((1 : ℝ) / 2) := h_cs
    _ ≤ (expect (fun x => |f x| ^ p)) ^ (1 / p) *
        (expect (fun x => |g x| ^ q)) ^ (1 / q) := by
        apply mul_le_mul h_hyp_f h_hyp_g
        · exact Real.rpow_nonneg (Hypercontractivity.expect_sq_noiseOp_nonneg _ _) _
        · exact Real.rpow_nonneg (Hypercontractivity.expect_rpow_abs_nonneg _ _) _

theorem weak_two_function_hypercontractivity
    (p q : ℝ) (hp1 : 1 ≤ p) (hp2 : p ≤ 2) (hq1 : 1 ≤ q) (hq2 : q ≤ 2)
    {n : ℕ} (f g : BooleanFunc n) :
    innerProduct f (noiseOp (Real.sqrt ((p - 1) * (q - 1))) g) ≤
    (expect (fun x => |f x| ^ p)) ^ (1 / p) *
    (expect (fun x => |g x| ^ q)) ^ (1 / q) := by
  have ρ_nonneg : 0 ≤ Real.sqrt ((p - 1) * (q - 1)) := by
    apply Real.sqrt_nonneg
  have p_sub : 0 ≤ p - 1 := by linarith
  have q_sub : 0 ≤ q - 1 := by linarith
  have p_le_one : p - 1 ≤ 1 := by linarith
  have q_le_one : q - 1 ≤ 1 := by linarith
  have ρ_le_one : Real.sqrt ((p - 1) * (q - 1)) ≤ 1 := by
    rw [Real.sqrt_le_one]
    nlinarith
  apply hypercontractivity_induction p q hp1 hq1 (Real.sqrt ((p - 1) * (q - 1))) (ρ_nonneg) (ρ_le_one) (weak_two_function_hypercontractivity_one_bit p q hp1 hp2 hq1 hq2) f g

end
end OneBitHypercontractivity
