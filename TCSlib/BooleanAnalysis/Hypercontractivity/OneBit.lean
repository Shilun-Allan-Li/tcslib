import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Data.Real.Sign
import TCSlib.BooleanAnalysis.Hypercontractivity.Bonami
import TCSlib.BooleanAnalysis.Hypercontractivity.Simple
/-
## Main results
- `(p, 2)-hypercontractivity on a single bit`:
  For f : BoolCube 1 → ℝ, 1 ≤ p ≤ 2, and 0 ≤ ρ with ρ² ≤ p − 1:
  (𝔼[(T_ρ f)²])^{1/2} ≤ (𝔼[|f|^p])^{1/p}
- `(2, q)-hypercontractivity on a single bit`:
  For g : BoolCube 1 → ℝ and q ≥ 2:
  ‖T_{1 / √(q - 1)} g‖_q ≤ ‖g‖_2
- `Weak (p, q) two-function hypercontractivity on a single bit`:
  For f, g : BoolCube 1 → ℝ, 1 ≤ p ≤ 2 ≤ q and ρ = √((p − 1)(q − 1)):
  ⟨f, T_ρ g⟩ ≤ (𝔼[|f|^p])^{1/p} · (𝔼[|g|^q])^{1/q}
- `Hypercontractivity induction theorem`:
  Hypercontractivity for n-bit functions follows from the one-bit case
-/
set_option maxHeartbeats 1600000

namespace OneBit

open BooleanAnalysis Real Bonami SimpleHypercontractivity

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

/--
**Lp norm monotonicity (power mean inequality)** on the Boolean cube:
For `1 ≤ r ≤ s` and `f : BoolCube n → ℝ`,
  `(𝔼[|f|^r])^{1/r} ≤ (𝔼[|f|^s])^{1/s}`
This is the power mean inequality for probability measures.
-/
lemma lp_norm_mono {n : ℕ} (r s : ℝ) (hr : 1 ≤ r) (hrs : r ≤ s)
    (f : BooleanFunc n) :
    (expect (fun x => |f x| ^ r)) ^ (1/r) ≤
    (expect (fun x => |f x| ^ s)) ^ (1/s) := by
  -- The weights `uniformWeight n` satisfy `∑ x, uniformWeight n = 1`, since there are `2^n` elements each with weight `(1/2)^n`.
  have h_weight_sum : ∑ x : BoolCube n, (uniformWeight n) = 1 := by
    simp +decide [ uniformWeight, Finset.card_univ ];
  have h_ineq : (∑ x : BoolCube n, (uniformWeight n) * |f x| ^ r) ≤ (∑ x : BoolCube n, (uniformWeight n) * |f x| ^ s) ^ (r / s) := by
    -- Apply Jensen's inequality for the concave function $x^{r/s}$.
    have h_jensen : (∑ x : BoolCube n, (uniformWeight n) * (|f x| ^ s) ^ (r / s)) ≤ ((∑ x : BoolCube n, (uniformWeight n) * |f x| ^ s)) ^ (r / s) := by
      have h_jensen : ConcaveOn ℝ (Set.Ici 0) (fun x : ℝ => x ^ (r / s)) := by
        exact ( Real.concaveOn_rpow ( by rw [ le_div_iff₀ ] <;> linarith ) ( by rw [ div_le_iff₀ ] <;> linarith ) );
      apply_rules [ h_jensen.le_map_sum ];
      · exact fun _ _ => by unfold uniformWeight; positivity;
      · exact fun _ _ => Real.rpow_nonneg ( abs_nonneg _ ) _;
    convert h_jensen using 3 ; rw [ ← Real.rpow_mul ( abs_nonneg _ ), mul_div_cancel₀ _ ( by linarith ) ];
  convert Real.rpow_le_rpow ( ?_ ) h_ineq ( show 0 ≤ 1 / r by positivity ) using 1;
  · unfold expect; norm_num [ mul_comm, Finset.mul_sum _ _ _ ] ;
  · rw [ ← Real.rpow_mul ( Finset.sum_nonneg fun _ _ => mul_nonneg ( by exact pow_nonneg ( by norm_num ) _ ) ( Real.rpow_nonneg ( abs_nonneg _ ) _ ) ) ] ; ring_nf;
    norm_num [ show r ≠ 0 by linarith, show s ≠ 0 by linarith, expect ];
    rw [ Finset.mul_sum _ _ _ ];
  · exact Finset.sum_nonneg fun _ _ => mul_nonneg ( by exact pow_nonneg ( by norm_num ) _ ) ( Real.rpow_nonneg ( abs_nonneg _ ) _ )

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
For `1 ≤ p ≤ 2`: `(p-1)^{p/2} ≤ 1`, which gives the inequality when `a = 0`.
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

/--
**Two-Point Inequality** (full version).
For `1 ≤ p ≤ 2` and all `a, b ∈ ℝ, 0 ≤ ρ, ρ² ≤ p − 1`:
  `(a² + ρ²b²)^{1/2} ≤ ((|a+b|^p + |a−b|^p) / 2)^{1/p}`
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
/--
**One-Bit (p, 2)-Hypercontractivity Theorem**.

For `f : BoolCube 1 → ℝ, 1 ≤ p ≤ 2`, and `0 ≤ ρ` with `ρ² ≤ p − 1`:
  `(𝔼[(T_ρ f)²])^{1/2} ≤ (𝔼[|f|^p])^{1/p}`
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

/-- sign(x) * x = |x| -/
private lemma sign_mul_self (x : ℝ) : Real.sign x * x = |x| := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [Real.sign_of_neg hx, abs_of_neg hx]; ring
  · simp [Real.sign_zero]
  · rw [Real.sign_of_pos hx, abs_of_pos hx, one_mul]

/-- |sign(x)| = 1 when x ≠ 0 -/
private lemma abs_sign_eq_one (x : ℝ) (hx : x ≠ 0) : |Real.sign x| = 1 := by
  rcases lt_or_gt_of_ne hx with h | h
  · simp [Real.sign_of_neg h]
  · simp [Real.sign_of_pos h]

/-- Expectation of pointwise nonneg function is nonneg -/
lemma expect_nonneg_of_nonneg {n : ℕ} {f : BooleanFunc n} (hf : ∀ x, 0 ≤ f x) :
    0 ≤ expect f := by
  unfold expect uniformWeight
  exact mul_nonneg (pow_nonneg (by positivity) _) (Finset.sum_nonneg (fun x _ => hf x))

/-- Expectation of constant function is the constant-/
private lemma expect_const_eq {n : ℕ} (c : ℝ) :
    expect (fun (_ : BoolCube n) => c) = c := by
  unfold expect uniformWeight
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_bool, Fintype.card_fin]

/--
Cauchy-Schwarz for the Boolean inner product
-/
lemma cauchy_schwarz_bool {n : ℕ} (f g : BooleanFunc n) :
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

/--
**Hölder sharpness**: For Hölder conjugate exponents `(p, q)`, for any function `u`,
there exists `f` with `‖f‖_p ≤ 1` and `‖u‖_q ≤ ⟨f, u⟩`.
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
**Noise operator duality**: (p, 2)-hypercontractivity implies (2, p')-hypercontractivity
where p' is the Hölder conjugate of p.
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
  `‖T_{1 / √(q - 1)} g‖_q ≤ ‖g‖_2`
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

end OneBit
