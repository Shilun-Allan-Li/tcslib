import Mathlib
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Order.Filter.Basic
import Mathlib.Algebra.BigOperators.Fin

set_option maxHeartbeats 0

set_option relaxedAutoImplicit false

set_option autoImplicit false

open Finset BigOperators Real

noncomputable section
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
          · norm_num [ Real.exp_ne_zero, Real.differentiableAt_exp, ne_of_gt ( show 0 < 1 - L + ( Real.exp η ) ⁻¹ * L from by cases lt_or_gt_of_ne hL <;> cases lt_or_gt_of_ne hL' <;> nlinarith [ inv_pos.mpr ( Real.exp_pos η ) ] ) ] ; ring;
            norm_num [ sq, mul_assoc, Real.exp_ne_zero ];
          · exact DifferentiableAt.log ( by norm_num [ Real.exp_ne_zero, Real.differentiableAt_exp ] ) ( by cases lt_or_gt_of_ne hL <;> cases lt_or_gt_of_ne hL' <;> nlinarith [ Real.exp_pos η, inv_pos.mpr ( Real.exp_pos η ), mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos η ) ) ] );
        exact fun x hx => DifferentiableAt.differentiableWithinAt ( by rw [ show deriv f = _ from funext h_deriv ] ; exact DifferentiableAt.add ( DifferentiableAt.add ( differentiableAt_const _ ) ( differentiableAt_id.div_const _ ) ) ( DifferentiableAt.div ( DifferentiableAt.mul ( differentiableAt_const _ ) ( Real.differentiableAt_exp.comp _ ( differentiableAt_id.neg ) ) ) ( by exact DifferentiableAt.add ( differentiableAt_const _ ) ( DifferentiableAt.mul ( differentiableAt_const _ ) ( Real.differentiableAt_exp.comp _ ( differentiableAt_id.neg ) ) ) ) ( by nlinarith [ Real.exp_pos ( -x ), mul_self_pos.mpr hL, mul_self_pos.mpr ( sub_ne_zero.mpr hL' ) ] ) ) );
      · -- Let's calculate the first derivative of $f$.
        have h_deriv : ∀ η, deriv f η = -L + η / 4 + L * Real.exp (-η) / (1 - L + L * Real.exp (-η)) := by
          intro η; erw [ deriv_sub ] <;> norm_num [ Real.exp_ne_zero, Real.exp_neg, Real.differentiableAt_exp, mul_comm L ];
          · norm_num [ Real.exp_ne_zero, Real.differentiableAt_exp, ne_of_gt ( show 0 < 1 - L + ( Real.exp η ) ⁻¹ * L from by cases lt_or_gt_of_ne hL <;> cases lt_or_gt_of_ne hL' <;> nlinarith [ inv_pos.mpr ( Real.exp_pos η ) ] ) ] ; ring;
            norm_num [ sq, mul_assoc, Real.exp_ne_zero ];
          · exact DifferentiableAt.log ( by norm_num [ Real.exp_ne_zero, Real.differentiableAt_exp ] ) ( by cases lt_or_gt_of_ne hL <;> cases lt_or_gt_of_ne hL' <;> nlinarith [ Real.exp_pos η, inv_pos.mpr ( Real.exp_pos η ), mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos η ) ) ] );
        -- Let's calculate the second derivative of $f$.
        have h_deriv2 : ∀ η, deriv^[2] f η = 1 / 4 - L * (1 - L) * Real.exp (-η) / (1 - L + L * Real.exp (-η))^2 := by
          norm_num [ funext h_deriv ];
          intro η; norm_num [ Real.exp_ne_zero, Real.exp_neg, Real.differentiableAt_exp, mul_comm L, ne_of_gt ( show 0 < 1 - L + L * Real.exp ( -η ) from by nlinarith [ Real.exp_pos ( -η ), mul_self_pos.mpr hL, mul_self_pos.mpr ( sub_ne_zero.mpr hL' ) ] ) ] ; ring;
          norm_num [ Real.exp_ne_zero, Real.differentiableAt_exp, ne_of_gt ( show 0 < 1 - L + L * ( Real.exp η ) ⁻¹ from by nlinarith [ Real.exp_pos η, mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos η ) ), mul_self_pos.mpr hL, mul_self_pos.mpr ( sub_ne_zero.mpr hL' ) ] ) ] ; ring;
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
end

set_option maxHeartbeats 0

set_option relaxedAutoImplicit false

set_option autoImplicit false

open Real Finset BigOperators

def LossSeq (N T : ℕ) := Fin T → Fin N → ℝ

def LossSeq.Valid {N T : ℕ} (ℓ : LossSeq N T) : Prop :=
  ∀ t i, 0 ≤ ℓ t i ∧ ℓ t i ≤ 1

noncomputable def cumLoss {N T : ℕ} (ℓ : LossSeq N T) (t : ℕ) (i : Fin N) : ℝ :=
  ((Finset.univ (α := Fin T)).filter (fun s => s.val < t)).sum (fun s => ℓ s i)

noncomputable def hedgeWeight {N T : ℕ} (η : ℝ) (ℓ : LossSeq N T) (t : ℕ) (i : Fin N) : ℝ :=
  Real.exp (-η * cumLoss ℓ t i)

noncomputable def potential {N T : ℕ} (η : ℝ) (ℓ : LossSeq N T) (t : ℕ) : ℝ :=
  ∑ i : Fin N, hedgeWeight η ℓ t i

noncomputable def hedgeDist {N T : ℕ} (η : ℝ) (ℓ : LossSeq N T) (t : ℕ) (i : Fin N) : ℝ :=
  hedgeWeight η ℓ t i / potential η ℓ t

noncomputable def hedgeLoss {N T : ℕ} (η : ℝ) (ℓ : LossSeq N T) (t : Fin T) : ℝ :=
  ∑ i : Fin N, hedgeDist η ℓ t.val i * ℓ t i

noncomputable def hedgeCumLoss {N T : ℕ} (η : ℝ) (ℓ : LossSeq N T) : ℝ :=
  ∑ t : Fin T, hedgeLoss η ℓ t

noncomputable def bestExpertLoss {N T : ℕ} (ℓ : LossSeq N T) : ℝ :=
  ⨅ i : Fin N, cumLoss ℓ T i

noncomputable def regret {N T : ℕ} (η : ℝ) (ℓ : LossSeq N T) : ℝ :=
  hedgeCumLoss η ℓ - bestExpertLoss ℓ

lemma potential_zero {N T : ℕ} [NeZero N] (η : ℝ) (ℓ : LossSeq N T) :
    potential η ℓ 0 = N := by
  simp only [potential, hedgeWeight, cumLoss]
  have hfilt : ∀ i : Fin N, ((Finset.univ (α := Fin T)).filter (fun s => s.val < 0)).sum
      (fun s => ℓ s i) = 0 := by
    intro i
    apply Finset.sum_eq_zero
    intro s hs
    simp [Finset.mem_filter] at hs
  simp only [hfilt, mul_zero, neg_zero, exp_zero, Finset.sum_const, Finset.card_fin]
  simp

lemma hedgeWeight_pos {N T : ℕ} (η : ℝ) (ℓ : LossSeq N T) (t : ℕ) (i : Fin N) :
    0 < hedgeWeight η ℓ t i := by
  exact exp_pos _

lemma potential_pos {N T : ℕ} [NeZero N] (η : ℝ) (ℓ : LossSeq N T) (t : ℕ) :
    0 < potential η ℓ t := by
  apply Finset.sum_pos
  · intro i _
    exact hedgeWeight_pos η ℓ t i
  · exact Finset.univ_nonempty

lemma exp_neg_le_linear {η x : ℝ} (hη : 0 < η) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp (-η * x) ≤ 1 - (1 - Real.exp (-η)) * x := by
  -- Convexity: exp(x·a + (1-x)·b) ≤ x·exp(a) + (1-x)·exp(b)
  -- Apply with a = -η, b = 0.
  have h1x : 0 ≤ 1 - x := sub_nonneg.mpr hx1
  have hconv := convexOn_exp.2 (Set.mem_univ (-η)) (Set.mem_univ 0) hx0 h1x
    (by linarith : x + (1 - x) = 1)
  simp only [smul_eq_mul, mul_zero, add_zero, exp_zero, mul_one] at hconv
  -- hconv : exp (x * -η) ≤ x * exp (-η) + (1 - x)
  -- Goal : exp (-η * x) ≤ 1 - (1 - exp (-η)) * x
  -- These are equal since x * -η = -η * x and x * exp(-η) + 1 - x = 1 - (1 - exp(-η)) * x
  have : x * -η = -η * x := by ring
  rw [this] at hconv
  linarith

lemma cumLoss_succ {N T : ℕ} (ℓ : LossSeq N T) (t : Fin T) (i : Fin N) :
    cumLoss ℓ (t.val + 1) i = cumLoss ℓ t.val i + ℓ t i := by
  simp only [cumLoss]
  -- The prefix `{s | s < t+1}` is the old prefix `{s | s < t}` plus the
  -- current round `t`.
  have : (Finset.univ (α := Fin T)).filter (fun s => s.val < t.val + 1) =
      ((Finset.univ).filter (fun s => s.val < t.val)) ∪ {t} := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_singleton]
    constructor
    · intro h; by_cases hs : s = t
      · exact Or.inr hs
      · left; omega
    · rintro (h | rfl)
      · omega
      · omega
  rw [this, Finset.sum_union]
  · simp
  · simp [Finset.disjoint_left]
    intro s hs
    omega

lemma cumLoss_horizon {N T : ℕ} (ℓ : LossSeq N T) (i : Fin N) :
    cumLoss ℓ T i = ∑ t : Fin T, ℓ t i := by
  simp only [cumLoss]
  congr 1
  ext t
  simp [t.isLt]

lemma hedgeWeight_succ {N T : ℕ} (η : ℝ) (ℓ : LossSeq N T) (t : Fin T) (i : Fin N) :
    hedgeWeight η ℓ (t.val + 1) i = hedgeWeight η ℓ t.val i * Real.exp (-η * ℓ t i) := by
  simp only [hedgeWeight, cumLoss_succ]
  ring_nf
  rw [← exp_add]
  ring_nf

lemma hedgeDist_sum {N T : ℕ} [NeZero N] (η : ℝ) (ℓ : LossSeq N T) (t : ℕ) :
    ∑ i : Fin N, hedgeDist η ℓ t i = 1 := by
  -- Normalization by the positive potential turns weights into a probability
  -- distribution.
  simp only [hedgeDist]
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (potential_pos η ℓ t))

lemma potential_ratio_le {N T : ℕ} [NeZero N] (η : ℝ) (hη : 0 < η)
    (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (t : Fin T) (ht : t.val + 1 ≤ T) :
    potential η ℓ (t.val + 1) / potential η ℓ t.val
      ≤ 1 - (1 - Real.exp (-η)) * hedgeLoss η ℓ t := by
  -- This is the core one-step Hedge estimate.  The only use of validity is
  -- that every coordinate of the current loss vector lies in `[0, 1]`.
  -- W_{t+1} = ∑_i w_t(i) · exp(-η · ℓ_t(i))
  -- W_{t+1}/W_t = ∑_i p_t(i) · exp(-η · ℓ_t(i))
  --            ≤ ∑_i p_t(i) · (1 - (1-e^{-η}) · ℓ_t(i))    [by exp_neg_le_linear]
  --            = 1 - (1-e^{-η}) · ∑_i p_t(i) · ℓ_t(i)
  --            = 1 - (1-e^{-η}) · hedgeLoss
  have hWt := potential_pos η ℓ t.val
  -- Rewrite W_{t+1}/W_t = ∑ p_t(i) · exp(-η · ℓ_t(i))
  -- Step 1: Rewrite potential ratio using weight factorization
  rw [div_le_iff₀ hWt]
  -- Goal: potential η ℓ (t+1) ≤ (1 - (1 - exp(-η)) * hedgeLoss η ℓ t) * potential η ℓ t
  -- W_{t+1} = ∑ w_t(i) * exp(-η * ℓ_t(i))
  have hW_succ : potential η ℓ (t.val + 1) =
      ∑ i : Fin N, hedgeWeight η ℓ t.val i * Real.exp (-η * ℓ t i) := by
    simp only [potential]; congr 1; ext i; exact hedgeWeight_succ η ℓ t i
  rw [hW_succ]
  -- Step 2: Apply exp_neg_le_linear to each term
  have hbound : ∀ i : Fin N,
      hedgeWeight η ℓ t.val i * Real.exp (-η * ℓ t i) ≤
      hedgeWeight η ℓ t.val i * (1 - (1 - Real.exp (-η)) * ℓ t i) := by
    intro i
    exact mul_le_mul_of_nonneg_left (exp_neg_le_linear hη (hℓ t i).1 (hℓ t i).2)
      (hedgeWeight_pos η ℓ t.val i).le
  -- Step 3: Sum up the bounds and show RHS = (1 - c * hedgeLoss) * W
  -- where c = 1 - exp(-η) and W = potential.
  -- RHS expanded: W - c * W * hedgeLoss = W - c * ∑(w_i * ℓ_i / W) * W = W - c * ∑ w_i * ℓ_i
  -- LHS ≤ ∑ w_i * (1 - c * ℓ_i) = ∑ w_i - c * ∑ w_i * ℓ_i = W - c * ∑ w_i * ℓ_i = RHS ✓
  set c := (1 : ℝ) - Real.exp (-η) with hc_def
  set W := potential η ℓ t.val with hW_def
  -- Expand the RHS
  have hW_ne : W ≠ 0 := ne_of_gt hWt
  -- hedgeLoss = (∑ w_i * ℓ_i) / W
  have hHL : hedgeLoss η ℓ t = (∑ i : Fin N, hedgeWeight η ℓ t.val i * ℓ t i) / W := by
    simp only [hedgeLoss, hedgeDist, hW_def, Finset.sum_div]
    congr 1; ext i; ring
  -- Goal: ∑ w_i * exp(-η * ℓ_i) ≤ (1 - c * hedgeLoss) * W
  -- ≤ ∑ w_i * (1 - c * ℓ_i) (from hbound)
  -- = ∑ w_i - c * ∑ w_i * ℓ_i
  -- = W - c * hedgeLoss * W = (1 - c * hedgeLoss) * W ✓
  have step1 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hbound i
  suffices ∑ i, hedgeWeight η ℓ t.val i * (1 - c * ℓ t i) =
      (1 - c * hedgeLoss η ℓ t) * W by linarith
  rw [hHL, hW_def, potential]
  have hW_ne : (∑ i : Fin N, hedgeWeight η ℓ t.val i) ≠ 0 := ne_of_gt hWt
  have : ∀ i : Fin N, hedgeWeight η ℓ t.val i * (1 - c * ℓ t i) =
      hedgeWeight η ℓ t.val i - c * (hedgeWeight η ℓ t.val i * ℓ t i) := by
    intro i; ring
  simp_rw [this, Finset.sum_sub_distrib, ← Finset.mul_sum]
  field_simp

lemma potential_ge_best_expert {N T : ℕ} [NeZero N] (η : ℝ) (hη : 0 < η)
    (ℓ : LossSeq N T) :
    potential η ℓ T ≥ Real.exp (-η * bestExpertLoss ℓ) := by
  -- The sum of all final weights is at least the single final weight of the
  -- best expert.  This is the lower-bound half of the potential method.
  simp only [bestExpertLoss, potential, ge_iff_le, hedgeWeight]
  -- ⨅ is achieved at some i₀ (Fin N is finite nonempty).
  obtain ⟨i₀, hi₀⟩ := Finite.exists_min (cumLoss ℓ T)
  -- hi₀ : ∀ j, cumLoss ℓ T i₀ ≤ cumLoss ℓ T j
  -- So cumLoss i₀ = ⨅ cumLoss.
  have hinf : ⨅ i, cumLoss ℓ T i = cumLoss ℓ T i₀ :=
    le_antisymm (ciInf_le ⟨_, by rintro _ ⟨j, rfl⟩; exact hi₀ j⟩ i₀) (le_ciInf hi₀)
  rw [hinf]
  -- Goal: exp(-η * cumLoss i₀) ≤ ∑ exp(-η * cumLoss i)
  exact Finset.single_le_sum (f := fun i => Real.exp (-η * cumLoss ℓ T i))
    (fun i _ => (exp_pos _).le) (Finset.mem_univ i₀)

lemma hedgeDist_nonneg {N T : ℕ} [NeZero N] (η : ℝ) (ℓ : LossSeq N T) (t : ℕ) (i : Fin N) :
    0 ≤ hedgeDist η ℓ t i :=
  div_nonneg (hedgeWeight_pos η ℓ t i).le (potential_pos η ℓ t).le

lemma hedgeLoss_le_one {N T : ℕ} [NeZero N] (η : ℝ) (ℓ : LossSeq N T) (hℓ : ℓ.Valid)
    (t : Fin T) : hedgeLoss η ℓ t ≤ 1 := by
  -- A convex combination of losses in `[0, 1]` is at most `1`.
  have hsum : hedgeLoss η ℓ t ≤ ∑ i : Fin N, hedgeDist η ℓ t.val i * 1 := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (hℓ t i).2 (hedgeDist_nonneg η ℓ t.val i)
  simp only [mul_one] at hsum
  linarith [hedgeDist_sum η ℓ t.val]

lemma hedgeLoss_nonneg {N T : ℕ} [NeZero N] (η : ℝ) (ℓ : LossSeq N T) (hℓ : ℓ.Valid)
    (t : Fin T) : 0 ≤ hedgeLoss η ℓ t := by
  -- A convex combination of nonnegative losses is nonnegative.
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (hedgeDist_nonneg η ℓ t.val i) (hℓ t i).1

lemma hoeffding_lemma {p h : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Real.log ((1 - p) + p * Real.exp h) ≤ p * h + h ^ 2 / 8 := by
  have hb := bernoulli_mgf_bound p (-h) hp0 hp1
  simp only [neg_neg] at hb
  linarith [show -p * -h + (-h) ^ 2 / 8 = p * h + h ^ 2 / 8 from by ring]

lemma log_potential_step_tight {N T : ℕ} [NeZero N] (η : ℝ) (hη : 0 < η)
    (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (t : Fin T) (ht : t.val + 1 ≤ T) :
    Real.log (potential η ℓ (t.val + 1)) - Real.log (potential η ℓ t.val)
      ≤ -η * hedgeLoss η ℓ t + η ^ 2 / 8 := by
  -- Here `μ = hedgeLoss` lies in `[0,1]`.  The one-step potential ratio is
  -- bounded by `(1-μ) + μ exp(-η)`, and Hoeffding converts the logarithm of
  -- that expression into `-η μ + η^2/8`.
  have hWt := potential_pos η ℓ t.val
  have hWt1 := potential_pos η ℓ (t.val + 1)
  rw [← Real.log_div (ne_of_gt hWt1) (ne_of_gt hWt)]
  have hratio := potential_ratio_le η hη ℓ hℓ t ht
  -- W_{t+1}/W_t ≤ (1-μ) + μ·e^{-η} where μ = hedgeLoss
  -- Apply Hoeffding with p = μ, h = -η
  set μ := hedgeLoss η ℓ t
  have hμ0 := hedgeLoss_nonneg η ℓ hℓ t
  have hμ1 := hedgeLoss_le_one η ℓ hℓ t
  have hratio_pos : 0 < potential η ℓ (t.val + 1) / potential η ℓ t.val :=
    div_pos hWt1 hWt
  -- The ratio is ≤ (1-μ) + μ·e^{-η}
  have hcomp : 1 - (1 - Real.exp (-η)) * μ = (1 - μ) + μ * Real.exp (-η) := by ring
  -- Apply log monotonicity then Hoeffding
  calc Real.log (potential η ℓ (t.val + 1) / potential η ℓ t.val)
      ≤ Real.log ((1 - μ) + μ * Real.exp (-η)) := by
        apply Real.log_le_log hratio_pos
        linarith [hcomp]
    _ ≤ μ * (-η) + (-η) ^ 2 / 8 :=
        hoeffding_lemma hμ0 hμ1
    _ = -η * μ + η ^ 2 / 8 := by ring

theorem hedge_regret_bound_tight {N T : ℕ} [NeZero N] (η : ℝ)
    (hη_pos : 0 < η)
    (ℓ : LossSeq N T) (hℓ : ℓ.Valid) :
    regret η ℓ ≤ Real.log N / η + η * T / 8 := by
  -- Same potential proof as `hedge_regret_bound`, but the tight step bound
  -- avoids the extra `η ≤ 1` assumption and improves the constant.
  -- Same structure as hedge_regret_bound but using the tight step bound.
  have hstep : ∀ t : Fin T, Real.log (potential η ℓ (t.val + 1)) - Real.log (potential η ℓ t.val)
      ≤ -η * hedgeLoss η ℓ t + η ^ 2 / 8 :=
    fun t => log_potential_step_tight η hη_pos ℓ hℓ t (by omega)
  -- Telescoping sum
  have hsum : Real.log (potential η ℓ T) - Real.log (potential η ℓ 0)
      ≤ -η * hedgeCumLoss η ℓ + η ^ 2 / 8 * T := by
    have hbounds := Finset.sum_le_sum fun t (_ : t ∈ Finset.univ) => hstep t
    have hrhs : ∑ t : Fin T, (-η * hedgeLoss η ℓ t + η ^ 2 / 8) =
        -η * hedgeCumLoss η ℓ + η ^ 2 / 8 * T := by
      simp only [hedgeCumLoss, Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_fin]
      ring
    suffices htel : ∑ t : Fin T,
        (Real.log (potential η ℓ (t.val + 1)) - Real.log (potential η ℓ t.val)) =
        Real.log (potential η ℓ T) - Real.log (potential η ℓ 0) by linarith
    set f := fun n => Real.log (potential η ℓ n)
    show ∑ t : Fin T, (f (t.val + 1) - f t.val) = f T - f 0
    conv_lhs => arg 2; ext t; rw [show t.val = (t : ℕ) from rfl]
    rw [Fin.sum_univ_eq_sum_range (fun n => f (n + 1) - f n)]
    exact Finset.sum_range_sub f T
  -- Use potential_zero and potential_ge_best_expert
  have hW0 : Real.log (potential η ℓ 0) = Real.log N := by rw [potential_zero]
  have hWT : Real.log (potential η ℓ T) ≥ -η * bestExpertLoss ℓ := by
    calc Real.log (potential η ℓ T) ≥ Real.log (Real.exp (-η * bestExpertLoss ℓ)) :=
          Real.log_le_log (exp_pos _) (potential_ge_best_expert η hη_pos ℓ)
      _ = -η * bestExpertLoss ℓ := Real.log_exp _
  -- Combine: η * regret ≤ log N + η²T/8
  unfold regret
  have hη_ne : η ≠ 0 := ne_of_gt hη_pos
  have hkey : η * (hedgeCumLoss η ℓ - bestExpertLoss ℓ)
      ≤ Real.log ↑N + η ^ 2 / 8 * ↑T := by nlinarith
  have hgoal : hedgeCumLoss η ℓ - bestExpertLoss ℓ ≤
      (Real.log ↑N + η ^ 2 / 8 * ↑T) / η := by
    rw [le_div_iff₀ hη_pos]; nlinarith
  calc hedgeCumLoss η ℓ - bestExpertLoss ℓ
      ≤ (Real.log ↑N + η ^ 2 / 8 * ↑T) / η := hgoal
    _ = Real.log ↑N / η + η * ↑T / 8 := by
        have : η ^ 2 / 8 * ↑T / η = η * ↑T / 8 := by
          rw [sq]; field_simp
        rw [add_div, this]

set_option maxHeartbeats 0

set_option relaxedAutoImplicit false

set_option autoImplicit false

open Real Finset BigOperators

structure ZeroSumGame (M N : ℕ) where
  payoff : Fin M → Fin N → ℝ
  payoff_nonneg : ∀ i j, 0 ≤ payoff i j
  payoff_le_one : ∀ i j, payoff i j ≤ 1

structure MixedStrategy (n : ℕ) where
  weights : Fin n → ℝ
  nonneg : ∀ i, 0 ≤ weights i
  sum_one : ∑ i : Fin n, weights i = 1

noncomputable def payoffVsPure {M N : ℕ} (G : ZeroSumGame M N)
    (p : MixedStrategy M) (j : Fin N) : ℝ :=
  ∑ i : Fin M, p.weights i * G.payoff i j

noncomputable def pureVsPayoff {M N : ℕ} (G : ZeroSumGame M N)
    (i : Fin M) (q : MixedStrategy N) : ℝ :=
  ∑ j : Fin N, G.payoff i j * q.weights j

noncomputable def bestColumn {M N : ℕ} [NeZero N] (G : ZeroSumGame M N)
    (p : MixedStrategy M) : Fin N :=
  Classical.choose (Finite.exists_min (payoffVsPure G p))

lemma bestColumn_spec {M N : ℕ} [NeZero N] (G : ZeroSumGame M N)
    (p : MixedStrategy M) (j : Fin N) :
    payoffVsPure G p (bestColumn G p) ≤ payoffVsPure G p j := by
  exact (Classical.choose_spec (Finite.exists_min (payoffVsPure G p))) j

noncomputable def ZeroSumGame.toLossSeq {M N T : ℕ} (G : ZeroSumGame M N)
    (colResponse : Fin T → Fin N) : LossSeq M T :=
  fun t i => 1 - G.payoff i (colResponse t)

lemma ZeroSumGame.toLossSeq_valid {M N T : ℕ} (G : ZeroSumGame M N)
    (colResponse : Fin T → Fin N) : (G.toLossSeq colResponse).Valid := by
  -- Payoffs in `[0,1]` make `1 - payoff` a valid Hedge loss.
  intro t i; simp only [ZeroSumGame.toLossSeq]
  exact ⟨by linarith [G.payoff_le_one i (colResponse t)],
         by linarith [G.payoff_nonneg i (colResponse t)]⟩

noncomputable def averageStrategy {n T : ℕ} [NeZero n] (hT : 0 < T)
    (strategies : Fin T → Fin n → ℝ)
    (h_nonneg : ∀ t i, 0 ≤ strategies t i)
    (h_sum : ∀ t, ∑ i : Fin n, strategies t i = 1) : MixedStrategy n where
  weights i := (∑ t : Fin T, strategies t i) / T
  nonneg i := div_nonneg (Finset.sum_nonneg fun t _ => h_nonneg t i) (Nat.cast_nonneg T)
  sum_one := by
    rw [← Finset.sum_div, Finset.sum_comm]
    simp_rw [h_sum, Finset.sum_const, Finset.card_fin, nsmul_eq_mul, mul_one]
    exact div_self (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hT))

noncomputable def empiricalStrategy {n T : ℕ} [NeZero n] (hT : 0 < T)
    (actions : Fin T → Fin n) : MixedStrategy n where
  weights i := (∑ t : Fin T, if actions t = i then (1 : ℝ) else 0) / T
  nonneg i := by
    apply div_nonneg
    · exact Finset.sum_nonneg fun t _ => by split <;> positivity
    · exact Nat.cast_nonneg T
  sum_one := by
    rw [← Finset.sum_div, Finset.sum_comm]
    have hinner : ∀ t : Fin T, ∑ i : Fin n, (if actions t = i then (1 : ℝ) else 0) = 1 := by
      intro t
      rw [Finset.sum_eq_single (actions t)]
      · simp
      · intro b _ hb
        simp [hb.symm]
      · intro h
        exact False.elim (h (Finset.mem_univ _))
    simp_rw [hinner, Finset.sum_const, Finset.card_fin, nsmul_eq_mul, mul_one]
    exact div_self (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hT))

lemma payoffVsPure_averageStrategy {M N T : ℕ} [NeZero M] (G : ZeroSumGame M N)
    (hT : 0 < T)
    (strategies : Fin T → Fin M → ℝ)
    (h_nonneg : ∀ t i, 0 ≤ strategies t i)
    (h_sum : ∀ t, ∑ i : Fin M, strategies t i = 1)
    (j : Fin N) :
    payoffVsPure G (averageStrategy hT strategies h_nonneg h_sum) j =
      (∑ t : Fin T, ∑ i : Fin M, strategies t i * G.payoff i j) / T := by
  simp only [payoffVsPure, averageStrategy]
  calc ∑ x : Fin M, (∑ t : Fin T, strategies t x) / ↑T * G.payoff x j
      = ∑ x : Fin M, (∑ t : Fin T, strategies t x * G.payoff x j) / ↑T := by
          congr 1
          ext x
          rw [← Finset.sum_mul]
          ring
    _ = (∑ x : Fin M, ∑ t : Fin T, strategies t x * G.payoff x j) / ↑T := by
          rw [Finset.sum_div]
    _ = (∑ t : Fin T, ∑ i : Fin M, strategies t i * G.payoff i j) / ↑T := by
          rw [Finset.sum_comm]

lemma pureVsPayoff_empiricalStrategy {M N T : ℕ} [NeZero N] (G : ZeroSumGame M N)
    (hT : 0 < T) (actions : Fin T → Fin N) (i : Fin M) :
    pureVsPayoff G i (empiricalStrategy hT actions) =
      (∑ t : Fin T, G.payoff i (actions t)) / T := by
  simp only [pureVsPayoff, empiricalStrategy]
  calc ∑ x : Fin N, G.payoff i x * ((∑ t : Fin T, if actions t = x then 1 else 0) / ↑T)
      = ∑ x : Fin N, (∑ t : Fin T, G.payoff i x *
            (if actions t = x then 1 else 0)) / ↑T := by
          congr 1
          ext x
          rw [← Finset.mul_sum]
          ring
    _ = (∑ x : Fin N, ∑ t : Fin T, G.payoff i x *
            (if actions t = x then 1 else 0)) / ↑T := by
          rw [Finset.sum_div]
    _ = (∑ t : Fin T, ∑ x : Fin N, G.payoff i x *
            (if actions t = x then 1 else 0)) / ↑T := by
          rw [Finset.sum_comm]
    _ = (∑ t : Fin T, G.payoff i (actions t)) / ↑T := by
          congr 1
          apply Finset.sum_congr rfl
          intro t _
          rw [Finset.sum_eq_single (actions t)]
          · simp
          · intro b _ hb
            simp [hb.symm]
          · intro h
            exact False.elim (h (Finset.mem_univ _))

noncomputable def prefixGameLoss {M N : ℕ} (G : ZeroSumGame M N)
    {t : ℕ} (actions : Fin t → Fin N) (i : Fin M) : ℝ :=
  ∑ s : Fin t, (1 - G.payoff i (actions s))

noncomputable def prefixHedgeWeight {M N : ℕ} (G : ZeroSumGame M N)
    (η : ℝ) {t : ℕ} (actions : Fin t → Fin N) (i : Fin M) : ℝ :=
  Real.exp (-η * prefixGameLoss G actions i)

noncomputable def prefixPotential {M N : ℕ} (G : ZeroSumGame M N)
    (η : ℝ) {t : ℕ} (actions : Fin t → Fin N) : ℝ :=
  ∑ i : Fin M, prefixHedgeWeight G η actions i

lemma prefixHedgeWeight_pos {M N : ℕ} (G : ZeroSumGame M N)
    (η : ℝ) {t : ℕ} (actions : Fin t → Fin N) (i : Fin M) :
    0 < prefixHedgeWeight G η actions i :=
  Real.exp_pos _

lemma prefixPotential_pos {M N : ℕ} [NeZero M] (G : ZeroSumGame M N)
    (η : ℝ) {t : ℕ} (actions : Fin t → Fin N) :
    0 < prefixPotential G η actions := by
  apply Finset.sum_pos
  · intro i _
    exact prefixHedgeWeight_pos G η actions i
  · exact Finset.univ_nonempty

noncomputable def prefixHedgeMixedStrategy {M N : ℕ} [NeZero M] (G : ZeroSumGame M N)
    (η : ℝ) {t : ℕ} (actions : Fin t → Fin N) : MixedStrategy M where
  weights i := prefixHedgeWeight G η actions i / prefixPotential G η actions
  nonneg i := div_nonneg (prefixHedgeWeight_pos G η actions i).le
    (prefixPotential_pos G η actions).le
  sum_one := by
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt (prefixPotential_pos G η actions))

noncomputable def hedgeResponseNat {M N : ℕ} [NeZero M] [NeZero N]
    (G : ZeroSumGame M N) (η : ℝ) : ℕ → Fin N
  | t =>
      bestColumn G
        (prefixHedgeMixedStrategy G η (t := t)
          (fun s : Fin t => hedgeResponseNat G η s.val))
termination_by t => t
decreasing_by
  exact s.isLt

lemma prefixGameLoss_eq_cumLoss {M N T : ℕ} (G : ZeroSumGame M N)
    (actions : Fin T → Fin N) (t : Fin T) (i : Fin M) :
    prefixGameLoss G (t := t.val) (fun s : Fin t.val => actions ⟨s.val, lt_trans s.isLt t.isLt⟩) i =
      cumLoss (G.toLossSeq actions) t.val i := by
  -- This identifies the recursive prefix view of the interaction with the
  -- `LossSeq` view expected by the generic Hedge theorem.
  simp only [prefixGameLoss, cumLoss, ZeroSumGame.toLossSeq]
  refine Finset.sum_bij
    (fun s (_ : s ∈ (Finset.univ : Finset (Fin t.val))) =>
      (⟨s.val, lt_trans s.isLt t.isLt⟩ : Fin T))
    ?mem ?eq ?inj ?surj
  · intro s _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact s.isLt
  · intro s _ b _ h
    have hv : (⟨s.val, lt_trans s.isLt t.isLt⟩ : Fin T).val =
        (⟨b.val, lt_trans b.isLt t.isLt⟩ : Fin T).val := congrArg Fin.val h
    exact Fin.ext hv
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    refine ⟨⟨b.val, hb⟩, Finset.mem_univ _, ?_⟩
    exact Fin.ext rfl
  · intro s _
    rfl

lemma prefixHedgeWeight_eq_hedgeWeight {M N T : ℕ} (G : ZeroSumGame M N)
    (η : ℝ) (actions : Fin T → Fin N) (t : Fin T) (i : Fin M) :
    prefixHedgeWeight G η
        (t := t.val) (fun s : Fin t.val => actions ⟨s.val, lt_trans s.isLt t.isLt⟩) i =
      hedgeWeight η (G.toLossSeq actions) t.val i := by
  simp only [prefixHedgeWeight, hedgeWeight]
  rw [prefixGameLoss_eq_cumLoss]

lemma prefixPotential_eq_potential {M N T : ℕ} (G : ZeroSumGame M N)
    (η : ℝ) (actions : Fin T → Fin N) (t : Fin T) :
    prefixPotential G η
        (t := t.val) (fun s : Fin t.val => actions ⟨s.val, lt_trans s.isLt t.isLt⟩) =
      potential η (G.toLossSeq actions) t.val := by
  simp only [prefixPotential, potential]
  apply Finset.sum_congr rfl
  intro i _
  exact prefixHedgeWeight_eq_hedgeWeight G η actions t i

lemma prefixHedgeMixedStrategy_weight_eq_hedgeDist {M N T : ℕ} [NeZero M]
    (G : ZeroSumGame M N) (η : ℝ) (actions : Fin T → Fin N) (t : Fin T) (i : Fin M) :
    (prefixHedgeMixedStrategy G η
        (t := t.val) (fun s : Fin t.val => actions ⟨s.val, lt_trans s.isLt t.isLt⟩)).weights i =
      hedgeDist η (G.toLossSeq actions) t.val i := by
  simp only [prefixHedgeMixedStrategy, hedgeDist]
  rw [prefixHedgeWeight_eq_hedgeWeight, prefixPotential_eq_potential]

lemma regret_to_payoff {M N T : ℕ} [NeZero M] (G : ZeroSumGame M N) (_hT : 0 < T)
    (p : Fin T → Fin M → ℝ)
    (hp_sum : ∀ t, ∑ i : Fin M, p t i = 1)
    (j : Fin T → Fin N)
    (R : ℝ)
    (hregret : (∑ t : Fin T, ∑ i : Fin M, p t i * (1 - G.payoff i (j t))) -
      ⨅ i : Fin M, (∑ t : Fin T, (1 - G.payoff i (j t))) ≤ R) :
    ∑ t : Fin T, ∑ i : Fin M, p t i * G.payoff i (j t) ≥
      ⨆ i : Fin M, ∑ t : Fin T, G.payoff i (j t) - R := by
  -- Regret is stated for losses, but the game is stated in payoffs.  Since
  -- loss is `1 - payoff`, the learner's loss regret becomes a payoff guarantee
  -- against the best fixed row action in hindsight.
  -- Rewrite the LHS of the hypothesis: ∑_t ∑_i p(t,i)*(1 - A(i,j_t)) = T - ∑_t ∑_i p(t,i)*A(i,j_t)
  have hlhs : ∑ t : Fin T, ∑ i : Fin M, p t i * (1 - G.payoff i (j t)) =
      ↑T - ∑ t : Fin T, ∑ i : Fin M, p t i * G.payoff i (j t) := by
    have h_inner : ∀ t : Fin T, ∑ i : Fin M, p t i * (1 - G.payoff i (j t)) =
        1 - ∑ i : Fin M, p t i * G.payoff i (j t) := by
      intro t
      have : ∑ i : Fin M, p t i * (1 - G.payoff i (j t)) =
          ∑ i : Fin M, (p t i - p t i * G.payoff i (j t)) := by
        congr 1; ext i; ring
      rw [this, sum_sub_distrib, hp_sum]
    simp_rw [h_inner, Finset.sum_sub_distrib]
    simp [Finset.sum_const, nsmul_eq_mul, mul_one]
  -- Rewrite the iInf: ⨅_i ∑_t (1 - A(i,j_t)) = T - ⨆_i ∑_t A(i,j_t)
  have hrhs : ⨅ i : Fin M, (∑ t : Fin T, (1 - G.payoff i (j t))) =
      ↑T - ⨆ i : Fin M, ∑ t : Fin T, G.payoff i (j t) := by
    have h_sum : ∀ i : Fin M, ∑ t : Fin T, (1 - G.payoff i (j t)) =
        ↑T - ∑ t : Fin T, G.payoff i (j t) := by
      intro i; simp [sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
    simp_rw [h_sum]
    have hbdd_above : BddAbove (Set.range (fun i : Fin M => ∑ t : Fin T, G.payoff i (j t))) :=
      Set.Finite.bddAbove (Set.finite_range _)
    have hbdd_below : BddBelow
        (Set.range (fun i : Fin M => ↑T - ∑ t : Fin T, G.payoff i (j t))) :=
      Set.Finite.bddBelow (Set.finite_range _)
    apply le_antisymm
    · -- ⨅ i, (T - f i) ≤ T - ⨆ i, f i  ↔  ⨆ i, f i ≤ T - ⨅ i, (T - f i)
      have hsup : ⨆ i : Fin M, ∑ t : Fin T, G.payoff i (j t) ≤
          ↑T - ⨅ i : Fin M, (↑T - ∑ t : Fin T, G.payoff i (j t)) :=
        ciSup_le fun i => by linarith [ciInf_le hbdd_below i]
      linarith
    · exact le_ciInf fun i => by linarith [le_ciSup hbdd_above i]
  -- Now the hypothesis becomes (T - S_pay) - (T - S_max) ≤ R, so S_max - S_pay ≤ R
  rw [hlhs, hrhs] at hregret
  -- The goal has ⨆ i, (∑ t, A(i,j_t) - R) which equals (⨆ i, ∑ t, A(i,j_t)) - R
  -- since R is constant w.r.t. i.
  rw [ge_iff_le]
  have hbdd_up : BddAbove (Set.range (fun i : Fin M => ∑ t : Fin T, G.payoff i (j t))) :=
    Set.Finite.bddAbove (Set.finite_range _)
  have hgoal_rw : ⨆ i : Fin M, (∑ t : Fin T, G.payoff i (j t) - R) =
      (⨆ i : Fin M, ∑ t : Fin T, G.payoff i (j t)) - R := by
    have hbdd : BddAbove (Set.range (fun i : Fin M => ∑ t : Fin T, G.payoff i (j t) - R)) :=
      Set.Finite.bddAbove (Set.finite_range _)
    apply le_antisymm
    · apply ciSup_le; intro i
      linarith [le_ciSup hbdd_up i]
    · rw [sub_le_iff_le_add]
      apply ciSup_le; intro i
      have := le_ciSup hbdd i
      linarith
  rw [hgoal_rw]
  linarith

private lemma hedge_construction {M N : ℕ} [NeZero M] [NeZero N] (G : ZeroSumGame M N)
    (_hM : 1 < M)
    (T : ℕ) (hT : 0 < T)
    (η : ℝ) (hη_pos : 0 < η) :
    ∃ (p : MixedStrategy M) (q : MixedStrategy N),
      ∀ (i : Fin M) (j : Fin N),
        payoffVsPure G p j + (Real.log M / η + η * T / 8) / T ≥
          pureVsPayoff G i q := by
  classical
  -- Generate the online column responses, turn them into Hedge losses, and
  -- record the row distributions used by Hedge at each round.
  let actions : Fin T → Fin N := fun t => hedgeResponseNat G η t.val
  let ℓ : LossSeq M T := G.toLossSeq actions
  let strategies : Fin T → Fin M → ℝ := fun t i => hedgeDist η ℓ t.val i
  have h_nonneg : ∀ t i, 0 ≤ strategies t i := by
    intro t i
    exact hedgeDist_nonneg η ℓ t.val i
  have h_sum : ∀ t, ∑ i : Fin M, strategies t i = 1 := by
    intro t
    exact hedgeDist_sum η ℓ t.val
  let p : MixedStrategy M := averageStrategy hT strategies h_nonneg h_sum
  let q : MixedStrategy N := empiricalStrategy hT actions
  refine ⟨p, q, ?_⟩
  intro i j
  set R : ℝ := Real.log ↑M / η + η * ↑T / 8
  -- Apply the tight Hedge bound to the generated loss sequence.
  have hvalid : ℓ.Valid := ZeroSumGame.toLossSeq_valid G actions
  have hreg := hedge_regret_bound_tight η hη_pos ℓ hvalid
  have hbestEq :
      bestExpertLoss ℓ =
        ⨅ i : Fin M, (∑ t : Fin T, (1 - G.payoff i (actions t))) := by
    unfold bestExpertLoss
    congr 1
    ext i
    rw [cumLoss_horizon]
    rfl
  have hreg' :
      (∑ t : Fin T, ∑ i : Fin M, strategies t i * (1 - G.payoff i (actions t))) -
        ⨅ i : Fin M, (∑ t : Fin T, (1 - G.payoff i (actions t))) ≤ R := by
    simpa only [R, regret, hedgeCumLoss, hedgeLoss, strategies, ℓ, ZeroSumGame.toLossSeq, hbestEq]
      using hreg
  -- Translate regret in losses into a payoff comparison with the best fixed
  -- row action against the generated columns.
  have hpay := regret_to_payoff G hT strategies h_sum actions R hreg'
  -- Each generated column is a best response to the current Hedge distribution,
  -- so replacing it by any fixed column `j` can only increase the row payoff.
  have hbest_round : ∀ t : Fin T,
      ∑ i : Fin M, strategies t i * G.payoff i (actions t) ≤
        ∑ i : Fin M, strategies t i * G.payoff i j := by
    intro t
    have hbc := bestColumn_spec G
      (prefixHedgeMixedStrategy G η
        (t := t.val) (fun s : Fin t.val => actions ⟨s.val, lt_trans s.isLt t.isLt⟩)) j
    have hleft :
        payoffVsPure G
          (prefixHedgeMixedStrategy G η
            (t := t.val) (fun s : Fin t.val => actions ⟨s.val, lt_trans s.isLt t.isLt⟩))
          (actions t)
          =
        ∑ i : Fin M, strategies t i * G.payoff i (actions t) := by
      unfold payoffVsPure
      apply Finset.sum_congr rfl
      intro k _
      have hwt := prefixHedgeMixedStrategy_weight_eq_hedgeDist G η actions t k
      rw [hwt]
    have hright :
        payoffVsPure G
          (prefixHedgeMixedStrategy G η
            (t := t.val) (fun s : Fin t.val => actions ⟨s.val, lt_trans s.isLt t.isLt⟩))
          j
          =
        ∑ i : Fin M, strategies t i * G.payoff i j := by
      unfold payoffVsPure
      apply Finset.sum_congr rfl
      intro k _
      have hwt := prefixHedgeMixedStrategy_weight_eq_hedgeDist G η actions t k
      rw [hwt]
    have haction :
        actions t =
          bestColumn G
            (prefixHedgeMixedStrategy G η
              (t := t.val) (fun s : Fin t.val => actions ⟨s.val, lt_trans s.isLt t.isLt⟩)) := by
      dsimp [actions]
      rw [hedgeResponseNat.eq_1]
    rw [← hleft, ← hright, haction]
    exact hbc
  have hbest_sum :
      ∑ t : Fin T, ∑ i : Fin M, strategies t i * G.payoff i (actions t) ≤
        ∑ t : Fin T, ∑ i : Fin M, strategies t i * G.payoff i j := by
    exact Finset.sum_le_sum fun t _ => hbest_round t
  -- Combine the payoff-regret guarantee with the best-response property, then
  -- divide by `T` and rewrite both sides as payoffs against `p` and `q`.
  have hi_sup : (∑ t : Fin T, G.payoff i (actions t)) - R ≤
      ⨆ i : Fin M, ∑ t : Fin T, G.payoff i (actions t) - R := by
    have hbdd : BddAbove (Set.range (fun i : Fin M => ∑ t : Fin T, G.payoff i (actions t) - R)) :=
      Set.Finite.bddAbove (Set.finite_range _)
    exact le_ciSup hbdd i
  have hmain_sum :
      ∑ t : Fin T, G.payoff i (actions t) - R ≤
        ∑ t : Fin T, ∑ i : Fin M, strategies t i * G.payoff i j := by
    linarith
  have hTpos : (0 : ℝ) < ↑T := Nat.cast_pos.mpr hT
  have hmain_div :
      (∑ t : Fin T, G.payoff i (actions t)) / ↑T - R / ↑T ≤
        (∑ t : Fin T, ∑ i : Fin M, strategies t i * G.payoff i j) / ↑T := by
    have := div_le_div_of_nonneg_right hmain_sum hTpos.le
    field_simp at this ⊢
    linarith
  have hpj :
      payoffVsPure G p j =
        (∑ t : Fin T, ∑ i : Fin M, strategies t i * G.payoff i j) / ↑T := by
    exact payoffVsPure_averageStrategy G hT strategies h_nonneg h_sum j
  have hqi :
      pureVsPayoff G i q =
        (∑ t : Fin T, G.payoff i (actions t)) / ↑T := by
    exact pureVsPayoff_empiricalStrategy G hT actions i
  dsimp [p, q]
  rw [hpj, hqi]
  dsimp [R]
  linarith
