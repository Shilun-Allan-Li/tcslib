/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import TCSlib.BooleanAnalysis.Hypercontractivity.Cube.FourthMoment

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Even-moment cube hypercontractivity

Coordinate decomposition and moment estimates for the forward noise operator.

## Main definitions

Shared definitions are imported; local technical helpers accompany their proofs.

## Main results

* `noise_l2_fourier`.
* `contractivity`.
* `binom_coeff_ineq`.
* `qth_moment_decomp`.
* `noise_qth_moment_decomp`.
* `hypercontractivity_2_2k`.
* `hypercontractivity_2_q`.
* `hypercontractivity_2_2`.
* `hypercontractivity_2_6`.
* `hypercontractivity_2_2k_rpow`.
* `innerProduct_eq_expect_sq`.
* `expect_sq_noiseOp_nonneg`.
* `expect_rpow_abs_nonneg`.
* `noiseOp_compose`.
* `hypercontractivity_p_2_general`.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014, §§9.3–10.1.
-/

open BooleanAnalysis MeasureTheory Set Filter ProbabilityTheory Real
open scoped BigOperators ENNReal Classical

namespace BooleanAnalysis.Hypercontractivity

variable {n : ℕ}

/-! ## Contractivity of the noise operator (q = 2 case) -/

/-- The L² norm of `T_ρ f` in Fourier space:
`𝔼[(T_ρ f)²] = ∑_S ρ^{2|S|} f̂(S)²`.
**Source:** [OD14, Thm. 9.17 (the `q = 2` case)]. -/
lemma noise_l2_fourier (ρ : ℝ) (f : BooleanFunc n) :
    innerProduct (noiseOp ρ f) (noiseOp ρ f) =
    ∑ S : Finset (Fin n), (ρ ^ S.card) ^ 2 * BooleanAnalysis.fourierCoeff f S ^ 2 := by
  rw [parseval]
  apply Finset.sum_congr rfl
  intro S _
  rw [noiseOp_fourier]
  ring

/-- **Contractivity**: `𝔼[(T_ρ f)²] ≤ 𝔼[f²]` for `ρ² ≤ 1`.
This is the `q = 2` case of hypercontractivity.
**Source:** [OD14, Thm. 9.17 (the `q = 2` case)].

**Proof sketch.** Parseval expresses both quadratic moments as sums of squared Fourier
coefficients. Noise multiplies each coefficient by a power of ρ, whose square is at most one.
Compare the nonnegative summands term by term.
-/
theorem contractivity (ρ : ℝ) (hρ : ρ ^ 2 ≤ 1) (f : BooleanFunc n) :
    expect (fun x => (noiseOp ρ f x) ^ 2) ≤ expect (fun x => f x ^ 2) := by
  have lhs : expect (fun x => (noiseOp ρ f x) ^ 2) =
      innerProduct (noiseOp ρ f) (noiseOp ρ f) := by
    simp [innerProduct, sq]
  have rhs : expect (fun x => f x ^ 2) = innerProduct f f := by
    simp [innerProduct, sq]
  rw [lhs, rhs, noise_l2_fourier, parseval]
  apply Finset.sum_le_sum
  intro S _
  have h1 : (ρ ^ S.card) ^ 2 = (ρ ^ 2) ^ S.card := by ring
  rw [h1]
  apply mul_le_of_le_one_left (sq_nonneg _)
  exact pow_le_one₀ (sq_nonneg ρ) hρ

/--
**Key combinatorial bound**: `C(2k, 2j) ≤ C(k, j) · (2k - 1)^j`.

This is proved by induction on `j`. The induction step shows
`C(2k, 2j) / C(2k, 2(j-1)) · 1/((2k-1) · C(k,j)/C(k,j-1))` ≤ 1,
which reduces to `(2k - 2j + 1) ≤ (2k - 1)(2j - 1)` for `j ≥ 1`.

**Source:** [OD14, Thm. 9.17 (even-moment proof)].

**Proof sketch.** Induct on j, using two successive binomial recurrences for the even-indexed
coefficient and one for the coefficient indexed by j. Compare the resulting factors using j < k
in the induction step, then combine this with the induction hypothesis and the next power of
2k − 1.
-/
lemma binom_coeff_ineq (k : ℕ) (hk : 1 ≤ k) (j : ℕ) (hj : j ≤ k) :
    Nat.choose (2 * k) (2 * j) ≤ Nat.choose k j * (2 * k - 1) ^ j := by
  induction j with
  | zero =>
    norm_num;
  | succ j ih => -- By the induction hypothesis, we have `C(2k, 2j) ≤ C(k, j) · (2k-1)^j`.
    have h_ind : Nat.choose (2 * k) (2 * j + 2) ≤ Nat.choose (2 * k) (2 * j) * ((2 * k - 2 * j) * (2 * k - 2 * j - 1)) / ((2 * j + 2) * (2 * j + 1)) := by
      rw [ Nat.le_div_iff_mul_le ];
      · have := Nat.choose_succ_right_eq ( 2 * k ) ( 2 * j );
        have := Nat.choose_succ_right_eq ( 2 * k ) ( 2 * j + 1 );
        rw [ show 2 * k - 2 * j - 1 = 2 * k - ( 2 * j + 1 ) by omega ];
        nlinarith [ Nat.sub_add_cancel ( by linarith : 2 * j ≤ 2 * k ), Nat.sub_add_cancel ( by linarith : 2 * j + 1 ≤ 2 * k ) ];
      · positivity;
    have h_ind_step : Nat.choose (2 * k) (2 * j) * ((2 * k - 2 * j) * (2 * k - 2 * j - 1)) ≤ Nat.choose k j * (2 * k - 1) ^ j * (k - j) * (2 * k - 1) * (2 * j + 2) := by
      have h_ind_step : (2 * k - 2 * j) * (2 * k - 2 * j - 1) ≤ (k - j) * (2 * k - 1) * (2 * j + 2) := by
        zify [ ← mul_tsub ];
        repeat rw [ Nat.cast_sub ] <;> push_cast <;> repeat linarith;
        · nlinarith [ sq ( k - j : ℤ ), sq ( j : ℤ ) ];
        · omega;
      simpa only [ mul_assoc ] using Nat.mul_le_mul ( ih ( Nat.le_of_succ_le hj ) ) h_ind_step;
    have h_final : Nat.choose k j * (k - j) * (2 * k - 1) * (2 * j + 2) ≤ Nat.choose k (j + 1) * (2 * k - 1) * (2 * j + 2) * (2 * j + 1) := by
      have h_final : Nat.choose k j * (k - j) ≤ Nat.choose k (j + 1) * (2 * j + 1) := by
        rw [← Nat.choose_succ_right_eq k j]
        apply Nat.mul_le_mul_left
        omega
      nlinarith only [ h_final, show 0 ≤ ( 2 * k - 1 ) * ( 2 * j + 2 ) by positivity ];
    refine le_trans h_ind ?_;
    refine Nat.div_le_of_le_mul ?_;
    refine le_trans h_ind_step ?_;
    convert Nat.mul_le_mul_right ( ( 2 * k - 1 ) ^ j ) h_final using 1 <;> ring

/-! ## Moment decomposition for even powers -/

/-- For even q, the q-th moment decomposes using avgLast and diffLast.
**Source:** [OD14, Thm. 9.17 (even-moment proof)]. -/
lemma qth_moment_decomp (q : ℕ) (f : BooleanFunc (n + 1)) :
    expect (fun x => f x ^ q) =
    expect (fun x' => ((avgLast f x' + diffLast f x') ^ q +
                       (avgLast f x' - diffLast f x') ^ q) / 2) := by
  unfold expect; rw [uniformWeight_succ];
  rw [show (∑ x : BoolCube (n + 1), f x ^ q) = ∑ x : BoolCube n, f (Fin.snoc x Bool.false) ^ q + ∑ x : BoolCube n, f (Fin.snoc x Bool.true) ^ q from ?_];
  · unfold avgLast diffLast; norm_num [Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_div]; ring_nf;
    norm_num [Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul]; ring_nf; rfl;
  · exact sum_boolCube_succ fun x => f x ^ q

/-- The noise operator decomposes on (n+1)-cubes for q-th moments.
**Source:** [OD14, Thm. 9.17 (even-moment proof)]. -/
lemma noise_qth_moment_decomp (q : ℕ) (ρ : ℝ) (f : BooleanFunc (n + 1)) :
    expect (fun x => (noiseOp ρ f x) ^ q) =
    expect (fun x' => ((noiseOp ρ (avgLast f) x' + ρ * noiseOp ρ (diffLast f) x') ^ q +
                       (noiseOp ρ (avgLast f) x' - ρ * noiseOp ρ (diffLast f) x') ^ q) / 2) := by
  convert (qth_moment_decomp q (noiseOp ρ f)) using 3;
  rw [show avgLast (noiseOp ρ f) = noiseOp ρ (avgLast f) from ?_,
      show diffLast (noiseOp ρ f) = ρ • noiseOp ρ (diffLast f) from ?_]; ring_nf!;
  · norm_num [Algebra.smul_def];
  · ext x; exact (by
    convert congr_arg (fun y => (y - (noiseOp ρ f (Fin.snoc x true))) / 2)
      (noiseOp_snoc ρ f x false) using 1; norm_num; ring_nf!;
    rw [show noiseOp ρ f (Fin.snoc x true) =
      noiseOp ρ (avgLast f) x + boolToSign true * ρ * noiseOp ρ (diffLast f) x
      from noiseOp_snoc ρ f x true]; norm_num; ring!;);
  · funext x; simp [avgLast, noiseOp]; unfold restrictLast; ring_nf;
    rw [noiseOp_snoc, noiseOp_snoc]; norm_num; ring!;

/-! ## The main (2, 2k)-Hypercontractivity Theorem -/

set_option maxHeartbeats 400000 in
/--
**The (2, 2k)-Hypercontractivity Theorem** (Bonami–Beckner):

For any Boolean function `f : {0,1}ⁿ → ℝ`, integer `k ≥ 1`,
and noise parameter `ρ` with `ρ² ≤ 1/(2k − 1)`:

`𝔼[(T_ρ f)^{2k}] ≤ (𝔼[f²])^k`.

Equivalently, `‖T_ρ f‖_{2k} ≤ ‖f‖₂`.
**Source:** [OD14, Thm. 9.17], specialized to even integer exponents.

**Proof sketch.** Induct on the dimension and expand the symmetric final-coordinate
decomposition; the odd terms cancel. Bound the remaining mixed moments by Hölder and the
induction hypothesis, treating the endpoints directly. The binomial-coefficient estimate bounds
their sum by (E[g²] + ρ²(2k − 1)E[h²])^k, which the noise restriction and second-moment
decomposition bound by the original second-moment power.
-/
theorem hypercontractivity_2_2k (k : ℕ) (hk : 1 ≤ k)
    (ρ : ℝ) (hρ : ρ ^ 2 ≤ 1 / ((2 : ℝ) * k - 1)) (f : BooleanFunc n) :
    expect (fun x => (noiseOp ρ f x) ^ (2 * k)) ≤ (expect (fun x => f x ^ 2)) ^ k := by
  revert f;
  induction n with
  | zero =>
    intro f
    have h_base : expect (fun x => (noiseOp ρ f x) ^ (2 * k)) = (expect (fun x => f x ^ (2 * k))) := by
      convert rfl using 3;
      convert rfl using 2;
      convert walsh_expansion f ‹_› |> Eq.symm using 1;
      exact Finset.sum_congr rfl fun x hx => by rw [ Finset.card_eq_zero.mpr ( Finset.eq_empty_of_forall_notMem fun y hy => by fin_cases y ) ] ; ring;
    simp_all +decide [ pow_mul ];
    unfold expect; norm_num [ Finset.card_univ ] ;
    norm_num [ uniformWeight ];
  | succ n ih =>
    intro f
    have h_decomp : expect (fun x => (noiseOp ρ f x) ^ (2 * k)) = ∑ j ∈ Finset.range (k + 1), Nat.choose (2 * k) (2 * j) * ρ ^ (2 * j) * expect (fun x' => (noiseOp ρ (avgLast f) x') ^ (2 * k - 2 * j) * (noiseOp ρ (diffLast f) x') ^ (2 * j)) := by
      have h_decomp : ∀ x' : BoolCube n, ((noiseOp ρ (avgLast f) x' + ρ * noiseOp ρ (diffLast f) x') ^ (2 * k) + (noiseOp ρ (avgLast f) x' - ρ * noiseOp ρ (diffLast f) x') ^ (2 * k)) / 2 = ∑ j ∈ Finset.range (k + 1), Nat.choose (2 * k) (2 * j) * ρ ^ (2 * j) * (noiseOp ρ (avgLast f) x') ^ (2 * k - 2 * j) * (noiseOp ρ (diffLast f) x') ^ (2 * j) := by
        intro x'
        have h_expand : ((noiseOp ρ (avgLast f) x' + ρ * noiseOp ρ (diffLast f) x') ^ (2 * k) + (noiseOp ρ (avgLast f) x' - ρ * noiseOp ρ (diffLast f) x') ^ (2 * k)) = ∑ j ∈ Finset.range (2 * k + 1), Nat.choose (2 * k) j * ρ ^ j * (noiseOp ρ (avgLast f) x') ^ (2 * k - j) * (noiseOp ρ (diffLast f) x') ^ j * (if j % 2 = 0 then 2 else 0) := by
          have h_expand : ((noiseOp ρ (avgLast f) x' + ρ * noiseOp ρ (diffLast f) x') ^ (2 * k) + (noiseOp ρ (avgLast f) x' - ρ * noiseOp ρ (diffLast f) x') ^ (2 * k)) = ∑ j ∈ Finset.range (2 * k + 1), Nat.choose (2 * k) j * ρ ^ j * (noiseOp ρ (avgLast f) x') ^ (2 * k - j) * (noiseOp ρ (diffLast f) x') ^ j + ∑ j ∈ Finset.range (2 * k + 1), Nat.choose (2 * k) j * (-ρ) ^ j * (noiseOp ρ (avgLast f) x') ^ (2 * k - j) * (noiseOp ρ (diffLast f) x') ^ j := by
            congr 1;
            · rw [ add_comm, add_pow ] ; congr ; ext ; ring;
            · rw [ sub_eq_add_neg, add_comm, add_pow ] ; congr ; ext ; ring;
          rw [ h_expand, ← Finset.sum_add_distrib ] ; refine' Finset.sum_congr rfl fun j hj => _ ; rcases Nat.even_or_odd' j with ⟨ c, rfl | rfl ⟩ <;> norm_num [ pow_add, pow_mul ] ; ring;
        rw [ h_expand, div_eq_iff ] <;> norm_num [ Finset.sum_ite ];
        rw [ Finset.sum_mul _ _ _ ];
        rw [ show Finset.filter ( fun x => x % 2 = 0 ) ( Finset.range ( 2 * k + 1 ) ) = Finset.image ( fun x => 2 * x ) ( Finset.range ( k + 1 ) ) from ?_, Finset.sum_image <| by norm_num ];
        ext ( _ | x ) <;> simp +arith +decide [ Nat.add_mod];
        exact ⟨ fun h => ⟨ ( x + 1 ) / 2, by omega, by omega ⟩, fun ⟨ a, ha, ha' ⟩ => ⟨ by omega, by omega ⟩ ⟩;
      rw [ noise_qth_moment_decomp ];
      simp +decide only [expect, h_decomp, mul_assoc, Finset.mul_sum _ _ _];
      exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring );
    -- By the induction hypothesis, we have:
    have h_ind : ∀ j ∈ Finset.range (k + 1), expect (fun x' => (noiseOp ρ (avgLast f) x') ^ (2 * k - 2 * j) * (noiseOp ρ (diffLast f) x') ^ (2 * j)) ≤ (expect (fun x' => (avgLast f x') ^ 2)) ^ (k - j) * (expect (fun x' => (diffLast f x') ^ 2)) ^ j := by
      intro j hj
      have h_ind_step : expect (fun x' => (noiseOp ρ (avgLast f) x') ^ (2 * k - 2 * j) * (noiseOp ρ (diffLast f) x') ^ (2 * j)) ≤ (expect (fun x' => (noiseOp ρ (avgLast f) x') ^ (2 * k))) ^ ((k - j) / k : ℝ) * (expect (fun x' => (noiseOp ρ (diffLast f) x') ^ (2 * k))) ^ (j / k : ℝ) := by
        have h_ind_step : ∀ (g h : BooleanFunc n), 0 ≤ expect (fun x' => g x' ^ (2 * k)) → 0 ≤ expect (fun x' => h x' ^ (2 * k)) → expect (fun x' => g x' ^ (2 * k - 2 * j) * h x' ^ (2 * j)) ≤ (expect (fun x' => g x' ^ (2 * k))) ^ ((k - j) / k : ℝ) * (expect (fun x' => h x' ^ (2 * k))) ^ (j / k : ℝ) := by
          intros g h hg hh
          have h_holder : ∀ (p q : ℝ), 1 < p → 1 < q → p⁻¹ + q⁻¹ = 1 → ∀ (f g : BoolCube n → ℝ), (∀ x', 0 ≤ f x') → (∀ x', 0 ≤ g x') → (∑ x', f x' * g x') ≤ (∑ x', f x' ^ p) ^ (1 / p : ℝ) * (∑ x', g x' ^ q) ^ (1 / q : ℝ) := by
            intros p q hp hq hpq f g hf hg;
            have := @Real.inner_le_Lp_mul_Lq;
            simpa only [ abs_of_nonneg ( hf _ ), abs_of_nonneg ( hg _ ) ] using this Finset.univ f g ( by constructor <;> ring_nf <;> nlinarith [ inv_pos.2 ( zero_lt_one.trans hp ), inv_pos.2 ( zero_lt_one.trans hq ), mul_inv_cancel₀ ( ne_of_gt ( zero_lt_one.trans hp ) ), mul_inv_cancel₀ ( ne_of_gt ( zero_lt_one.trans hq ) ) ] );
          by_cases hj : j = 0 ∨ j = k;
          · cases hj <;> simp +decide [ *, ne_of_gt ( zero_lt_one.trans_le hk ) ];
          · have h_holder : (∑ x', |g x'| ^ (2 * k - 2 * j) * |h x'| ^ (2 * j)) ≤ (∑ x', |g x'| ^ (2 * k)) ^ ((k - j) / k : ℝ) * (∑ x', |h x'| ^ (2 * k)) ^ (j / k : ℝ) := by
              convert h_holder ( k / ( k - j ) ) ( k / j ) _ _ _ ( fun x' => |g x'| ^ ( 2 * k - 2 * j ) ) ( fun x' => |h x'| ^ ( 2 * j ) ) _ _ using 1 <;> norm_num;
              · congr! 2;
                · refine' Finset.sum_congr rfl fun x' _ => _;
                  rw [ ← Real.rpow_natCast _ ( 2 * k - 2 * j ), ← Real.rpow_mul ( abs_nonneg _ ) ] ; norm_num [ Nat.cast_sub ( show 2 * j ≤ 2 * k from by linarith [ Finset.mem_range.mp ‹_› ] ) ];
                  rw [ show ( 2 * k - 2 * j : ℝ ) * ( k / ( k - j ) ) = 2 * k by rw [ mul_div, div_eq_iff ] <;> nlinarith [ show ( j : ℝ ) < k from mod_cast lt_of_le_of_ne ( Finset.mem_range_succ_iff.mp ‹_› ) ( by tauto ) ] ] ; norm_cast;
                · refine' Finset.sum_congr rfl fun x' _ => _;
                  rw [ ← Real.rpow_natCast _ ( 2 * j ), ← Real.rpow_mul ( abs_nonneg _ ) ] ; ring_nf ; norm_num [ show j ≠ 0 by tauto ];
                  norm_num [ mul_assoc, mul_comm, mul_left_comm, show j ≠ 0 by tauto ];
                  norm_cast;
              · rw [ lt_div_iff₀ ] <;> norm_num;
                · exact Nat.pos_of_ne_zero fun h => hj <| Or.inl h;
                · exact lt_of_le_of_ne ( Finset.mem_range_succ_iff.mp ‹_› ) ( by tauto );
              · rw [ lt_div_iff₀ ] <;> norm_cast <;> cases lt_or_gt_of_ne ( mt Or.inl hj ) <;> cases lt_or_gt_of_ne ( mt Or.inr hj ) <;> linarith [ Finset.mem_range.mp ‹_› ];
              · rw [ ← add_div, div_eq_iff ] <;> norm_num ; linarith;
            convert mul_le_mul_of_nonneg_left h_holder ( show 0 ≤ uniformWeight n by exact pow_nonneg ( by norm_num ) _ ) using 1 <;> norm_num [ expect ];
            · norm_num [ pow_mul ];
              exact Or.inl ( Finset.sum_congr rfl fun _ _ => by rw [ abs_eq_max_neg, max_def ] ; split_ifs <;> simp +decide [ *, Nat.even_sub ( show 2 * j ≤ 2 * k from by linarith [ Finset.mem_range.mp ‹_› ] ) ] );
            · norm_num [ pow_mul, abs_mul, abs_pow ];
              rw [ Real.mul_rpow ( by exact pow_nonneg ( by norm_num ) _ ) ( Finset.sum_nonneg fun _ _ => by positivity ), Real.mul_rpow ( by exact pow_nonneg ( by norm_num ) _ ) ( Finset.sum_nonneg fun _ _ => by positivity ) ] ; ring_nf;
              norm_num [ mul_assoc, mul_comm, mul_left_comm, ne_of_gt ( zero_lt_one.trans_le hk ) ];
              rw [ ← mul_assoc, ← Real.rpow_add ( by exact pow_pos ( by norm_num ) _ ) ] ; norm_num [ show k ≠ 0 by linarith ];
        apply h_ind_step;
        · exact mul_nonneg ( pow_nonneg ( by norm_num ) _ ) ( Finset.sum_nonneg fun _ _ => pow_mul ( noiseOp ρ ( avgLast f ) _ ) 2 k ▸ by positivity );
        · exact mul_nonneg ( pow_nonneg ( by norm_num ) _ ) ( Finset.sum_nonneg fun _ _ => pow_mul ( noiseOp ρ ( diffLast f ) _ ) 2 k ▸ by positivity );
      refine le_trans h_ind_step ?_;
      gcongr;
      · refine' Real.rpow_nonneg _ _;
        exact mul_nonneg ( pow_nonneg ( by norm_num ) _ ) ( Finset.sum_nonneg fun _ _ => pow_mul ( noiseOp ρ ( diffLast f ) _ ) 2 k ▸ by positivity );
      · exact pow_nonneg (expect_sq_nonneg (avgLast f)) _;
      · refine' le_trans ( Real.rpow_le_rpow ( _ ) ( ih _ ) ( _ ) ) _;
        · exact mul_nonneg ( by exact pow_nonneg ( by norm_num ) _ ) ( Finset.sum_nonneg fun _ _ => pow_mul ( noiseOp ρ ( avgLast f ) _ ) 2 k ▸ by positivity );
        · exact div_nonneg ( sub_nonneg_of_le ( Nat.cast_le.mpr ( Finset.mem_range_succ_iff.mp hj ) ) ) ( Nat.cast_nonneg _ );
        · rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( expect_sq_nonneg _ ), mul_comm ];
          rw [ div_mul_cancel₀ _ ( by positivity ), ← Nat.cast_sub ( Finset.mem_range_succ_iff.mp hj ) ] ; norm_cast;
      · convert Real.rpow_le_rpow ( ?_ ) ( ih ( diffLast f ) ) ( show ( 0 : ℝ ) ≤ j / k by positivity ) using 1;
        · rw [ ← Real.rpow_natCast _ k, ← Real.rpow_mul (expect_sq_nonneg (diffLast f)), mul_div_cancel₀ _ ( by positivity ), Real.rpow_natCast ];
        · exact le_of_not_gt fun h => by have := expect_sq_nonneg ( fun x => noiseOp ρ ( diffLast f ) x ^ k ) ; norm_num [ pow_mul' ] at * ; linarith;
    -- By the binomial coefficient inequality, we have:
    have h_binom : ∀ j ∈ Finset.range (k + 1), Nat.choose (2 * k) (2 * j) * ρ ^ (2 * j) ≤ Nat.choose k j * (ρ ^ 2 * (2 * k - 1)) ^ j := by
      intros j hj
      have h_binom_coeff : Nat.choose (2 * k) (2 * j) ≤ Nat.choose k j * (2 * k - 1) ^ j := by
        apply binom_coeff_ineq k hk j (Finset.mem_range_succ_iff.mp hj);
      convert mul_le_mul_of_nonneg_right ( Nat.cast_le.mpr h_binom_coeff ) ( pow_mul ρ 2 j ▸ by positivity : 0 ≤ ρ ^ ( 2 * j ) ) using 1 ; ring_nf;
      rw [ Nat.cast_mul, Nat.cast_pow, Nat.cast_sub ( by linarith ) ] ; push_cast ; ring_nf;
      rw [ show ( -ρ ^ 2 + ρ ^ 2 * k * 2 : ℝ ) = ρ ^ 2 * ( -1 + k * 2 ) by ring ] ; rw [ mul_pow ] ; ring;
    -- By combining the results from the decomposition, induction hypothesis, and binomial coefficient inequality, we get:
    have h_combined : expect (fun x => (noiseOp ρ f x) ^ (2 * k)) ≤ ∑ j ∈ Finset.range (k + 1), Nat.choose k j * (ρ ^ 2 * (2 * k - 1)) ^ j * (expect (fun x' => (avgLast f x') ^ 2)) ^ (k - j) * (expect (fun x' => (diffLast f x') ^ 2)) ^ j := by
      rw [h_decomp];
      refine Finset.sum_le_sum fun j hj => ?_;
      refine le_trans ( mul_le_mul_of_nonneg_left ( h_ind j hj ) ?_ ) ?_;
      · exact mul_nonneg ( Nat.cast_nonneg _ ) ( pow_mul ρ 2 j ▸ by positivity );
      · simpa only [ mul_assoc ] using mul_le_mul_of_nonneg_right ( h_binom j hj ) ( mul_nonneg ( pow_nonneg ( expect_sq_nonneg _ ) _ ) ( pow_nonneg ( expect_sq_nonneg _ ) _ ) );
    -- By the binomial theorem, we have:
    have h_binom_theorem : ∑ j ∈ Finset.range (k + 1), Nat.choose k j * (ρ ^ 2 * (2 * k - 1)) ^ j * (expect (fun x' => (avgLast f x') ^ 2)) ^ (k - j) * (expect (fun x' => (diffLast f x') ^ 2)) ^ j = (expect (fun x' => (avgLast f x') ^ 2) + ρ ^ 2 * (2 * k - 1) * expect (fun x' => (diffLast f x') ^ 2)) ^ k := by
      rw [ add_comm, add_pow ];
      rw [ add_comm, ← Finset.sum_flip ];
      refine' Finset.sum_congr rfl fun x hx => _;
      rw [ Nat.choose_symm ( Finset.mem_range_succ_iff.mp hx ), tsub_tsub_cancel_of_le ( Finset.mem_range_succ_iff.mp hx ) ] ; ring_nf;
      rw [ show ( -ρ ^ 2 + ρ ^ 2 * k * 2 : ℝ ) = ( ρ ^ 2 * k * 2 - ρ ^ 2 ) by ring ] ; rw [ show ( ρ ^ 2 * k * expect ( fun x' => diffLast f x' ^ 2 ) * 2 - ρ ^ 2 * expect ( fun x' => diffLast f x' ^ 2 ) ) = ( ρ ^ 2 * k * 2 - ρ ^ 2 ) * expect ( fun x' => diffLast f x' ^ 2 ) by ring ] ; rw [ mul_pow ] ; ring;
    refine le_trans h_combined <| h_binom_theorem.le.trans ?_;
    gcongr;
    · exact add_nonneg ( expect_sq_nonneg _ ) ( mul_nonneg ( mul_nonneg ( sq_nonneg _ ) ( sub_nonneg.mpr ( by norm_cast; linarith ) ) ) ( expect_sq_nonneg _ ) );
    · rw [ second_moment_decomp ];
      rw [ le_div_iff₀ ] at hρ <;> nlinarith [ show ( k : ℝ ) ≥ 1 by norm_cast, show ( expect fun x' => diffLast f x' ^ 2 ) ≥ 0 by exact expect_sq_nonneg _ ]

/-! ## Equivalent formulation with q -/

/-- The (2, q)-Hypercontractivity restated with even `q`.
**Source:** [OD14, Thm. 9.17], specialized to even integer exponents. -/
theorem hypercontractivity_2_q (q : ℕ) (hq : 2 ≤ q) (hq_even : Even q)
    (ρ : ℝ) (hρ : ρ ^ 2 ≤ 1 / ((q : ℝ) - 1)) (f : BooleanFunc n) :
    expect (fun x => (noiseOp ρ f x) ^ q) ≤ (expect (fun x => f x ^ 2)) ^ (q / 2) := by
  obtain ⟨k, rfl⟩ := hq_even
  have hk : 1 ≤ k := by omega
  simp only [show k + k = 2 * k from by ring, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  apply hypercontractivity_2_2k k hk ρ _ f
  convert hρ using 1
  push_cast; ring

/-! ## Corollaries and specific cases -/

/-- The (2, 2)-hypercontractivity is just contractivity.
**Source:** [OD14, Thm. 9.17], specialized to `q = 2`. -/
theorem hypercontractivity_2_2 (ρ : ℝ) (hρ : ρ ^ 2 ≤ 1) (f : BooleanFunc n) :
    expect (fun x => (noiseOp ρ f x) ^ 2) ≤ (expect (fun x => f x ^ 2)) ^ 1 := by
  rw [pow_one]
  exact contractivity ρ hρ f

/-- (2, 6)-hypercontractivity.
**Source:** [OD14, Prop. 9.16]. -/
theorem hypercontractivity_2_6 (ρ : ℝ) (hρ : ρ ^ 2 ≤ 1 / 5) (f : BooleanFunc n) :
    expect (fun x => (noiseOp ρ f x) ^ 6) ≤ (expect (fun x => f x ^ 2)) ^ 3 := by
  exact hypercontractivity_2_q 6 (by norm_num) ⟨3, by ring⟩ ρ (by linarith) f

/-! ## Real-power formulation -/
/--
(2, 2k)-hypercontractivity in `‖·‖_{2k} ≤ ‖·‖_2` form.
**Source:** [OD14, Thm. 9.17], specialized to even integer exponents. -/
theorem hypercontractivity_2_2k_rpow (k : ℕ) (hk : 1 ≤ k)
    (ρ : ℝ) (hρ : ρ ^ 2 ≤ 1 / ((2 : ℝ) * k - 1)) (f : BooleanFunc n) :
    (expect (fun x => (noiseOp ρ f x) ^ (2 * k))) ^ (1 / (2 * k : ℝ)) ≤
    (expect (fun x => f x ^ 2)) ^ (1 / 2 : ℝ) := by
  convert Real.rpow_le_rpow ( ?_ ) ( hypercontractivity_2_2k k ( by linarith ) ( ρ ) ?_ ( f ) ) ?_ using 1;
  · rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( expect_sq_nonneg _ ) ] ; ring_nf ; norm_num [ show k ≠ 0 by linarith ];
  · convert expect_sq_nonneg ( fun x => noiseOp ρ f x ^ k ) using 1;
    exact congr_arg _ ( funext fun x => by ring );
  · exact hρ;
  · positivity

/-! ## (p, 2)-Hypercontractivity via Duality -/

/-- Identifies a Boolean-cube inner product with its squared `L²` norm.

**Source:** [OD14, Prop. 9.19 (proof)]. -/
lemma innerProduct_eq_expect_sq (f : BooleanFunc n) :
    innerProduct f f = BooleanAnalysis.expect (fun x => f x ^ 2) := by
  unfold innerProduct BooleanAnalysis.expect uniformWeight
  congr 1
  apply Finset.sum_congr rfl
  intro x _; ring

/-- Shows that the squared `L²` moment of a noisy Boolean function is nonnegative.

**Source:** [OD14, Prop. 9.19 (proof)]. -/
lemma expect_sq_noiseOp_nonneg (ρ : ℝ) (f : BooleanFunc n) :
    0 ≤ BooleanAnalysis.expect (fun x => (noiseOp ρ f x) ^ 2) := by
  unfold BooleanAnalysis.expect uniformWeight
  apply mul_nonneg (pow_nonneg (by positivity) _)
  apply Finset.sum_nonneg
  intro x _; positivity

/-- Shows that an absolute real-power moment is nonnegative.

**Source:** [OD14, Prop. 9.19 (proof)]. -/
lemma expect_rpow_abs_nonneg (p : ℝ) (f : BooleanFunc n) :
    0 ≤ BooleanAnalysis.expect (fun x => |f x| ^ p) := by
  unfold BooleanAnalysis.expect uniformWeight
  apply mul_nonneg (pow_nonneg (by positivity) _)
  apply Finset.sum_nonneg
  intro x _; positivity

/-- Composing noise operators multiplies their parameter
**Source:** [OD14, Prop. 9.19 (proof)]. -/
lemma noiseOp_compose (ρ σ : ℝ) (f : BooleanFunc n) :
    noiseOp ρ (noiseOp σ f) = noiseOp (ρ * σ) f := by
  ext x
  simp only [noiseOp]
  congr 1; ext S
  rw [noiseOp_fourier]; ring

/--
**The (p, 2)-Hypercontractivity Theorem** (general duality framework):
Derives a `(p, 2)` hypercontractive bound from a `(2, q)` bound by duality.

**Source:** [OD14, Prop. 9.19].

**Proof sketch.** Use self-adjointness to express the squared noisy L² norm as the inner product
with the twice-noised function. The supplied Hölder inequality and (2,q) estimate bound this by
the original L^p norm times the noisy L² norm. Handle zero noisy norm directly and otherwise
cancel it.
-/
theorem hypercontractivity_p_2_general
    {ρ : ℝ} {p q : ℝ}
    (_hp : 1 < p) (hq : 2 ≤ q)
    (_hpq : 1/p + 1/q = 1)
    (f : BooleanFunc n)
    (holder : ∀ (u v : BooleanFunc n),
      innerProduct u v ≤
      (BooleanAnalysis.expect (fun x => |u x| ^ p)) ^ (1/p) *
      (BooleanAnalysis.expect (fun x => |v x| ^ q)) ^ (1/q))
    (hyp_2_q : ∀ (g : BooleanFunc n),
      BooleanAnalysis.expect (fun x => |noiseOp ρ g x| ^ q) ≤
      (BooleanAnalysis.expect (fun x => g x ^ 2)) ^ (q/2)) :
    (BooleanAnalysis.expect (fun x => (noiseOp ρ f x) ^ 2)) ^ (1/2 : ℝ) ≤
    (BooleanAnalysis.expect (fun x => |f x| ^ p)) ^ (1/p) := by
  set E₂ := BooleanAnalysis.expect (fun x => (noiseOp ρ f x) ^ 2)
  have hE₂_nn : 0 ≤ E₂ := expect_sq_noiseOp_nonneg ρ f
  by_cases hE₂_zero : E₂ = 0
  · rw [hE₂_zero]
    simp only [Real.zero_rpow (by norm_num : (1:ℝ)/2 ≠ 0)]
    exact Real.rpow_nonneg (expect_rpow_abs_nonneg p f) _
  have hE₂_pos : 0 < E₂ := lt_of_le_of_ne hE₂_nn (Ne.symm hE₂_zero)
  have h_inner : innerProduct (noiseOp ρ f) (noiseOp ρ f) = E₂ := by
    rw [innerProduct_eq_expect_sq]
  have h_self_adj : E₂ = innerProduct f (noiseOp ρ (noiseOp ρ f)) := by
    rw [← h_inner, noiseOp_self_adjoint]
  have h_holder := holder f (noiseOp ρ (noiseOp ρ f))
  have hq_pos : 0 < q := by linarith
  have h_Lq_bound :
      (BooleanAnalysis.expect (fun x => |noiseOp ρ (noiseOp ρ f) x| ^ q)) ^ (1/q) ≤
      E₂ ^ (1/2 : ℝ) := by
    have step1 : (BooleanAnalysis.expect (fun x => |noiseOp ρ (noiseOp ρ f) x| ^ q)) ^ (1/q) ≤
        ((BooleanAnalysis.expect (fun x => (noiseOp ρ f x) ^ 2)) ^ (q/2)) ^ (1/q) := by
      apply Real.rpow_le_rpow
        (expect_rpow_abs_nonneg q (noiseOp ρ (noiseOp ρ f)))
        (hyp_2_q (noiseOp ρ f))
        (by positivity)
    have step2 : ((BooleanAnalysis.expect (fun x => (noiseOp ρ f x) ^ 2)) ^ (q/2)) ^ (1/q) =
        E₂ ^ (1/2 : ℝ) := by
      rw [← Real.rpow_mul hE₂_nn]
      congr 1; field_simp
    linarith
  have main_bound : E₂ ≤
      (BooleanAnalysis.expect (fun x => |f x| ^ p)) ^ (1/p) * E₂ ^ (1/2 : ℝ) := by
    calc E₂ = innerProduct f (noiseOp ρ (noiseOp ρ f)) := h_self_adj
      _ ≤ (BooleanAnalysis.expect (fun x => |f x| ^ p)) ^ (1/p) *
          (BooleanAnalysis.expect (fun x => |noiseOp ρ (noiseOp ρ f) x| ^ q)) ^ (1/q) :=
        h_holder
      _ ≤ (BooleanAnalysis.expect (fun x => |f x| ^ p)) ^ (1/p) * E₂ ^ (1/2 : ℝ) := by
          apply mul_le_mul_of_nonneg_left h_Lq_bound
          exact Real.rpow_nonneg (expect_rpow_abs_nonneg p f) _
  have h_half_pos : 0 < E₂ ^ (1/2 : ℝ) := Real.rpow_pos_of_pos hE₂_pos _
  have h_split : E₂ ^ (1/2 : ℝ) * E₂ ^ (1/2 : ℝ) = E₂ := by
    rw [← Real.rpow_add hE₂_pos]; norm_num
  have step3 : E₂ ^ (1/2 : ℝ) * E₂ ^ (1/2 : ℝ) ≤
      (BooleanAnalysis.expect (fun x => |f x| ^ p)) ^ (1/p) * E₂ ^ (1/2 : ℝ) := by
    rw [h_split]; exact main_bound
  exact le_of_mul_le_mul_right step3 h_half_pos

end BooleanAnalysis.Hypercontractivity
