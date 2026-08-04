import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Real.StarOrdered
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

open Finset BigOperators Real

noncomputable section

/-!
# Hoeffding's Lemma and Log-MGF Bound

## Main results

- `exp_convexity_bound'`: For x ∈ [0,1], exp(-η·x) ≤ 1 - x + x·exp(-η) by convexity of exp.
- `weighted_exp_le_affine`: Weighted sum bound Σ pᵢ·exp(-η·ℓᵢ) ≤ 1 - (1-exp(-η))·L using convexity.
- `log_one_add_le`: For u > -1, ln(1+u) ≤ u.
- `eta_exp_bound`: For η ≥ 0, η - 1 + exp(-η) ≤ η²/2.
- `hoeffding_log_mgf_weak`: Weak log-MGF bound ln(Σ pᵢ·exp(-η·ℓᵢ)) ≤ -η·L + η²/2.
- `bernoulli_mgf_bound`: Bernoulli MGF bound ln(1 - L + L·exp(-η)) ≤ -L·η + η²/8.
- `hoeffding_log_mgf_tight`: Tight log-MGF bound ln(Σ pᵢ·exp(-η·ℓᵢ)) ≤ -η·L + η²/8.

## References

- Original formalization by Arhaan Aggarwal
-/

-- ============================================================================
-- Auxiliary lemmas
-- ============================================================================

/-- For x ∈ [0,1], x(1-x) ≤ 1/4. -/
lemma mul_one_sub_le_quarter (x : ℝ) (_hx0 : 0 ≤ x) (_hx1 : x ≤ 1) :
    x * (1 - x) ≤ 1 / 4 := by
  linarith [sq_nonneg (x - 1 / 2)]

/-
By convexity of exp, for x ∈ [0,1]: exp(-ηx) ≤ 1 - x + x·exp(-η).
-/
theorem exp_convexity_bound' (η x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp (-η * x) ≤ 1 - x + x * Real.exp (-η) := by
  -- We'll use that exponential functions are convex to show this inequality.
  have h_convex : ConvexOn ℝ (Set.univ : Set ℝ) Real.exp := by
    exact convexOn_exp;
  have := h_convex.2 ( Set.mem_univ 0 ) ( Set.mem_univ ( -η ) );
  convert @this ( 1 - x ) x ( by linarith ) ( by linarith ) ( by linarith ) using 1 <;> norm_num ; ring

/-
Weighted sum bound using convexity.
-/
theorem weighted_exp_le_affine
    {n : ℕ}
    (p : Fin n → ℝ) (hp_nonneg : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1)
    (ℓ : Fin n → ℝ) (hℓ_nonneg : ∀ i, 0 ≤ ℓ i) (hℓ_le : ∀ i, ℓ i ≤ 1)
    (η : ℝ) :
    ∑ i, p i * Real.exp (-η * ℓ i) ≤
      1 - (1 - Real.exp (-η)) * (∑ i, p i * ℓ i) := by
  -- Apply the convexity bound to each term in the sum.
  have h_term_bound : ∀ i, p i * Real.exp (-η * ℓ i) ≤ p i * (1 - ℓ i + ℓ i * Real.exp (-η)) := by
    exact fun i => mul_le_mul_of_nonneg_left ( exp_convexity_bound' η ( ℓ i ) ( hℓ_nonneg i ) ( hℓ_le i ) ) ( hp_nonneg i );
  convert Finset.sum_le_sum fun i _ => h_term_bound i using 1 ; ring_nf;
  simpa [ Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum _ _ _, ← Finset.sum_mul, hp_sum ] using by ring;

/-- For u > -1, ln(1+u) ≤ u. -/
theorem log_one_add_le (u : ℝ) (hu : -1 < u) :
    Real.log (1 + u) ≤ u := by
  linarith [Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + u)]

/-
For η ≥ 0, η - 1 + exp(-η) ≤ η²/2.
-/
theorem eta_exp_bound (η : ℝ) (hη : 0 ≤ η) :
    η - 1 + Real.exp (-η) ≤ η ^ 2 / 2 := by
  -- Define the function $f(η) = η^2/2 - η + 1 - e^{-η}$.
  set f : ℝ → ℝ := fun η => η^2 / 2 - η + 1 - Real.exp (-η);
  -- We'll use the fact that $f(η)$ is differentiable and that its derivative is non-negative for $η ≥ 0$.
  have h_deriv_nonneg : ∀ η ≥ 0, deriv f η ≥ 0 := by
    intro η hη; erw [ deriv_sub ] <;> norm_num [ Real.exp_neg, Real.differentiableAt_exp ];
    rw [ div_le_iff₀ ] <;> nlinarith [ Real.exp_pos η, Real.exp_neg η, mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos η ) ), Real.add_one_le_exp η, Real.add_one_le_exp ( -η ) ];
  by_contra h_contra;
  -- Apply the mean value theorem to $f$ on the interval $[0, η]$.
  obtain ⟨c, hc⟩ : ∃ c ∈ Set.Ioo 0 η, deriv f c = (f η - f 0) / (η - 0) := by
    apply_rules [ exists_deriv_eq_slope ];
    · exact hη.lt_of_ne ( by rintro rfl; norm_num at h_contra );
    · fun_prop;
    · fun_prop;
  norm_num +zetaDelta at *;
  nlinarith [ h_deriv_nonneg c hc.1.1.le, mul_div_cancel₀ ( η ^ 2 / 2 - η + 1 - Real.exp ( -η ) ) ( by linarith : η ≠ 0 ) ]

/-
============================================================================
Weak Hoeffding bound (η²/2 constant)
============================================================================

The log-MGF bound with η²/2 constant (weaker than tight η²/8):
    ln(Σ p_i · exp(-η · ℓ_i)) ≤ -η · L + η²/2
-/
theorem hoeffding_log_mgf_weak
    {n : ℕ} (_hn : 0 < n)
    (p : Fin n → ℝ) (hp_nonneg : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1)
    (ℓ : Fin n → ℝ) (hℓ_nonneg : ∀ i, 0 ≤ ℓ i) (hℓ_le : ∀ i, ℓ i ≤ 1)
    (η : ℝ) (hη : 0 < η) :
    Real.log (∑ i, p i * Real.exp (-η * ℓ i)) ≤
      -η * (∑ i, p i * ℓ i) + η ^ 2 / 2 := by
  -- By weighted_exp_le_affine, Σ p_i · exp(-η·ℓ_i) ≤ 1 - (1-exp(-η))·L.
  have h_affine : ∑ i, p i * Real.exp (-η * ℓ i) ≤ 1 - (1 - Real.exp (-η)) * (∑ i, p i * ℓ i) := by
    exact weighted_exp_le_affine p hp_nonneg hp_sum ℓ hℓ_nonneg hℓ_le η;
  nontriviality;
  refine' le_trans ( Real.log_le_log ( _ ) h_affine ) _;
  · by_contra h_neg;
    -- Since $\sum_{i} p_i \exp(-η \ell_i) \leq 0$, we have $p_i \exp(-η \ell_i) = 0$ for all $i$.
    have h_zero : ∀ i, p i * Real.exp (-η * ℓ i) = 0 := by
      exact fun i => le_antisymm ( le_trans ( Finset.single_le_sum ( fun i _ => mul_nonneg ( hp_nonneg i ) ( Real.exp_nonneg ( -η * ℓ i ) ) ) ( Finset.mem_univ i ) ) ( le_of_not_gt h_neg ) ) ( mul_nonneg ( hp_nonneg i ) ( Real.exp_nonneg _ ) );
    simp_all +decide [ ne_of_gt ( Real.exp_pos _ ) ];
  · refine' le_trans ( Real.log_le_sub_one_of_pos _ ) _;
    · exact sub_pos_of_lt ( by nlinarith [ Real.exp_pos ( -η ), Real.exp_lt_one_iff.2 ( show -η < 0 by linarith ), show ∑ i, p i * ℓ i ≤ 1 by exact hp_sum ▸ Finset.sum_le_sum fun i _ => mul_le_of_le_one_right ( hp_nonneg i ) ( hℓ_le i ) ] );
    · nlinarith [ show 0 ≤ ∑ i, p i * ℓ i from Finset.sum_nonneg fun _ _ => mul_nonneg ( hp_nonneg _ ) ( hℓ_nonneg _ ), show ∑ i, p i * ℓ i ≤ 1 from by rw [ ← hp_sum ] ; exact Finset.sum_le_sum fun i _ => mul_le_of_le_one_right ( hp_nonneg i ) ( hℓ_le i ), Real.add_one_le_exp ( -η ), Real.exp_pos ( -η ), eta_exp_bound η hη.le ]

/-
============================================================================
Tight Hoeffding bound (η²/8 constant)
============================================================================

Key Bernoulli MGF bound (Hoeffding's lemma for Bernoulli):
    For L ∈ [0,1] and η ∈ ℝ:
    ln(1 - L + L · exp(-η)) ≤ -L · η + η²/8

    Proof: Define φ(η) = -Lη + η²/8 - ln(1-L+L·e^{-η}).
    Then φ(0) = 0, φ'(0) = 0, and φ''(η) = 1/4 - q(1-q) ≥ 0 where
    q = L·e^{-η}/(1-L+L·e^{-η}) ∈ (0,1). So φ is convex with minimum at 0,
    hence φ ≥ 0.
-/
theorem bernoulli_mgf_bound (L η : ℝ) (hL0 : 0 ≤ L) (hL1 : L ≤ 1) :
    Real.log (1 - L + L * Real.exp (-η)) ≤ -L * η + η ^ 2 / 8 := by
  -- Define the function $f(η) = -Lη + η²/8 - \ln(1 - L + L·e^{-η})$.
  set f : ℝ → ℝ := fun η => -L * η + η^2 / 8 - Real.log (1 - L + L * Real.exp (-η));
  by_cases hL : L = 0 <;> by_cases hL' : L = 1 <;> simp_all +decide;
  · positivity;
  · positivity;
  · -- We'll use the fact that $f(η)$ is convex and has a minimum at $η = 0$.
    have h_convex : ConvexOn ℝ (Set.univ : Set ℝ) f := by
      apply_rules [ convexOn_of_deriv2_nonneg, convex_univ ];
      · exact continuousOn_of_forall_continuousAt fun x _ => by exact ContinuousAt.sub ( ContinuousAt.add ( continuousAt_const.mul continuousAt_id ) ( continuousAt_id.pow 2 |> ContinuousAt.div_const <| 8 ) ) ( ContinuousAt.log ( continuousAt_const.add ( continuousAt_const.mul ( Real.continuous_exp.continuousAt.comp <| ContinuousAt.neg continuousAt_id ) ) ) <| by cases lt_or_gt_of_ne hL <;> cases lt_or_gt_of_ne hL' <;> nlinarith [ Real.exp_pos ( -x ) ] ) ;
      · exact DifferentiableOn.sub ( DifferentiableOn.add ( differentiableOn_id.const_mul _ ) ( differentiableOn_id.pow 2 |> DifferentiableOn.div_const <| 8 ) ) ( DifferentiableOn.log ( DifferentiableOn.add ( differentiableOn_const _ ) ( DifferentiableOn.mul ( differentiableOn_const _ ) ( DifferentiableOn.exp ( differentiableOn_id.neg ) ) ) ) fun x hx => by cases lt_or_gt_of_ne hL <;> cases lt_or_gt_of_ne hL' <;> nlinarith [ Real.exp_pos ( -x ) ] );
      · -- Let's calculate the first derivative of $f$.
        have h_deriv : ∀ η, deriv f η = -L + η / 4 + L * Real.exp (-η) / (1 - L + L * Real.exp (-η)) := by
          intro η; erw [ deriv_sub ] <;> norm_num [ Real.exp_ne_zero, Real.exp_neg, Real.differentiableAt_exp, mul_comm L ];
          · norm_num [ Real.exp_ne_zero, Real.differentiableAt_exp, ne_of_gt ( show 0 < 1 - L + ( Real.exp η ) ⁻¹ * L from by cases lt_or_gt_of_ne hL <;> cases lt_or_gt_of_ne hL' <;> nlinarith [ inv_pos.mpr ( Real.exp_pos η ) ] ) ] ; ring_nf;
            norm_num [ sq, mul_assoc, Real.exp_ne_zero ];
          · exact DifferentiableAt.log ( by norm_num [ Real.exp_ne_zero, Real.differentiableAt_exp ] ) ( by cases lt_or_gt_of_ne hL <;> cases lt_or_gt_of_ne hL' <;> nlinarith [ Real.exp_pos η, inv_pos.mpr ( Real.exp_pos η ), mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos η ) ) ] );
        exact fun x hx => DifferentiableAt.differentiableWithinAt ( by rw [ show deriv f = _ from funext h_deriv ] ; exact DifferentiableAt.add ( DifferentiableAt.add ( differentiableAt_const _ ) ( differentiableAt_id.div_const _ ) ) ( DifferentiableAt.div ( DifferentiableAt.mul ( differentiableAt_const _ ) ( Real.differentiableAt_exp.comp _ ( differentiableAt_id.neg ) ) ) ( by exact DifferentiableAt.add ( differentiableAt_const _ ) ( DifferentiableAt.mul ( differentiableAt_const _ ) ( Real.differentiableAt_exp.comp _ ( differentiableAt_id.neg ) ) ) ) ( by nlinarith [ Real.exp_pos ( -x ), mul_self_pos.mpr hL, mul_self_pos.mpr ( sub_ne_zero.mpr hL' ) ] ) ) );
      · -- Let's calculate the first derivative of $f$.
        have h_deriv : ∀ η, deriv f η = -L + η / 4 + L * Real.exp (-η) / (1 - L + L * Real.exp (-η)) := by
          intro η; erw [ deriv_sub ] <;> norm_num [ Real.exp_ne_zero, Real.exp_neg, Real.differentiableAt_exp, mul_comm L ];
          · norm_num [ Real.exp_ne_zero, Real.differentiableAt_exp, ne_of_gt ( show 0 < 1 - L + ( Real.exp η ) ⁻¹ * L from by cases lt_or_gt_of_ne hL <;> cases lt_or_gt_of_ne hL' <;> nlinarith [ inv_pos.mpr ( Real.exp_pos η ) ] ) ] ; ring_nf;
            norm_num [ sq, mul_assoc, Real.exp_ne_zero ];
          · exact DifferentiableAt.log ( by norm_num [ Real.exp_ne_zero, Real.differentiableAt_exp ] ) ( by cases lt_or_gt_of_ne hL <;> cases lt_or_gt_of_ne hL' <;> nlinarith [ Real.exp_pos η, inv_pos.mpr ( Real.exp_pos η ), mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos η ) ) ] );
        -- Let's calculate the second derivative of $f$.
        have h_deriv2 : ∀ η, deriv^[2] f η = 1 / 4 - L * (1 - L) * Real.exp (-η) / (1 - L + L * Real.exp (-η))^2 := by
          norm_num [ funext h_deriv ];
          intro η; norm_num [ Real.exp_ne_zero, Real.exp_neg, Real.differentiableAt_exp, mul_comm L, ne_of_gt ( show 0 < 1 - L + L * Real.exp ( -η ) from by nlinarith [ Real.exp_pos ( -η ), mul_self_pos.mpr hL, mul_self_pos.mpr ( sub_ne_zero.mpr hL' ) ] ) ] ; ring_nf;
          norm_num [ Real.exp_ne_zero, Real.differentiableAt_exp, ne_of_gt ( show 0 < 1 - L + L * ( Real.exp η ) ⁻¹ from by nlinarith [ Real.exp_pos η, mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos η ) ), mul_self_pos.mpr hL, mul_self_pos.mpr ( sub_ne_zero.mpr hL' ) ] ) ] ; ring_nf;
          grind;
        simp +zetaDelta at *;
        intro η; rw [ h_deriv2 ] ; norm_num;
        rw [ div_le_iff₀ ] <;> nlinarith [ sq_nonneg ( 1 - L - L * Real.exp ( -η ) ), show 0 < L * Real.exp ( -η ) by positivity, show 0 < 1 - L by exact sub_pos.mpr ( lt_of_le_of_ne hL1 hL' ), Real.exp_pos ( -η ) ];
    have h_min : ∀ η, f η ≥ f 0 + deriv f 0 * (η - 0) := by
      intro η; have := h_convex.2 ( Set.mem_univ 0 ) ( Set.mem_univ η ) ; simp_all +decide ;
      -- Apply the definition of the derivative to get the inequality.
      have h_deriv : Filter.Tendsto (fun t => (f (t * η) - f 0) / t) (nhdsWithin 0 (Set.Ioi 0)) (nhds (deriv f 0 * η)) := by
        have h_deriv : HasDerivAt (fun t => f (t * η)) (deriv f 0 * η) 0 := by
          convert HasDerivAt.comp 0 ( show HasDerivAt f _ _ from hasDerivAt_deriv_iff.mpr ?_ ) ( HasDerivAt.mul ( hasDerivAt_id 0 ) ( hasDerivAt_const _ _ ) ) using 1 <;> norm_num;
          exact DifferentiableAt.sub ( DifferentiableAt.add ( differentiableAt_id.const_mul _ ) ( by norm_num ) ) ( DifferentiableAt.log ( by exact DifferentiableAt.add ( differentiableAt_const _ ) ( DifferentiableAt.mul ( differentiableAt_const _ ) ( Real.differentiableAt_exp.comp _ ( differentiableAt_id.neg ) ) ) ) ( by cases lt_or_gt_of_ne hL <;> cases lt_or_gt_of_ne hL' <;> nlinarith [ Real.exp_pos ( -0 ) ] ) );
        simpa [ div_eq_inv_mul ] using h_deriv.tendsto_slope_zero_right;
      have h_deriv_le : ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0), (f (t * η) - f 0) / t ≤ f η - f 0 := by
        filter_upwards [ Ioo_mem_nhdsGT_of_mem ⟨ le_rfl, zero_lt_one ⟩ ] with t ht using by have := this ( show 0 ≤ 1 - t by linarith [ ht.2 ] ) ( show 0 ≤ t by linarith [ ht.1 ] ) ( by linarith [ ht.1, ht.2 ] ) ; rw [ div_le_iff₀ ( by linarith [ ht.1 ] ) ] ; nlinarith [ ht.1, ht.2 ] ;
      exact le_of_tendsto h_deriv h_deriv_le |> fun h => by linarith;
    simp +zetaDelta at *;
    norm_num [ Real.exp_neg, Real.differentiableAt_exp, mul_comm L ] at *;
    exact h_min η

/-
The tight Hoeffding log-MGF bound:
    ln(Σ p_i · exp(-η · ℓ_i)) ≤ -η · (Σ p_i · ℓ_i) + η²/8

    Proof: By convexity of exp, Σ p_i · exp(-η·ℓ_i) ≤ 1 - L + L·exp(-η)
    (where L = Σ p_i · ℓ_i), then apply bernoulli_mgf_bound.
-/
theorem hoeffding_log_mgf_tight
    {n : ℕ} (_hn : 0 < n)
    (p : Fin n → ℝ) (hp_nonneg : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1)
    (ℓ : Fin n → ℝ) (hℓ_nonneg : ∀ i, 0 ≤ ℓ i) (hℓ_le : ∀ i, ℓ i ≤ 1)
    (η : ℝ) (_hη : 0 < η) :
    Real.log (∑ i, p i * Real.exp (-η * ℓ i)) ≤
      -η * (∑ i, p i * ℓ i) + η ^ 2 / 8 := by
  -- By weighted_exp_le_affine, Σ p_i · exp(-η·ℓ_i) ≤ 1 - L + L·exp(-η) where L = Σ p_i·ℓ_i.
  have h1 : ∑ i, p i * Real.exp (-η * ℓ i) ≤ 1 - (1 - Real.exp (-η)) * (∑ i, p i * ℓ i) := by
    convert weighted_exp_le_affine p hp_nonneg hp_sum ℓ hℓ_nonneg hℓ_le η using 1;
  refine' le_trans ( Real.log_le_log ( _ ) h1 ) _;
  · -- Since $p$ is a probability distribution, there exists some $i$ such that $p_i > 0$.
    obtain ⟨i, hi⟩ : ∃ i, 0 < p i := by
      exact not_forall_not.mp fun h => by have := hp_sum ▸ Finset.sum_nonpos fun i _ => le_of_not_gt fun hi => h i hi; norm_num at this;
    exact lt_of_lt_of_le ( mul_pos hi ( Real.exp_pos _ ) ) ( Finset.single_le_sum ( fun i _ => mul_nonneg ( hp_nonneg i ) ( Real.exp_nonneg _ ) ) ( Finset.mem_univ i ) );
  · convert bernoulli_mgf_bound ( ∑ i, p i * ℓ i ) η _ _ using 1 <;> ring_nf;
    · exact Finset.sum_nonneg fun _ _ => mul_nonneg ( hp_nonneg _ ) ( hℓ_nonneg _ );
    · exact hp_sum ▸ Finset.sum_le_sum fun i _ => mul_le_of_le_one_right ( hp_nonneg i ) ( hℓ_le i )

end
