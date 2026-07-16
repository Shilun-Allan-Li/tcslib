/-
Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karim Abdel Sadek, Mark Bedaywi
-/
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
import TCSlib.LearningTheory.Hedge.Hoeffding

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

open Real Finset BigOperators

/-!
# Hedge Algorithm: No-Regret Guarantee

## Main results

- `hedge_regret_bound`: For any valid loss sequence with N experts, T rounds, and η ∈ (0,1], the regret of Hedge is at most (ln N)/η + ηT/2.
- `hedge_regret_bound_tight`: For any valid loss sequence with N experts, T rounds, and η > 0, the regret of Hedge is at most (ln N)/η + ηT/8.
- `hedge_regret_optimal`: With optimal η = √(2 ln N / T), regret ≤ √(2 T ln N).
- `hedge_regret_tight_optimal`: With η = √(8 log N / T), the tight Hedge bound gives regret ≤ √((T/2) log N).
- `hedge_no_regret`: Average regret ≤ √(2 ln N / T) → 0 as T → ∞.
- `hoeffding_lemma`: For p ∈ [0,1] and any h ∈ ℝ, ln((1-p) + p·eʰ) ≤ p·h + h²/8.

## References

- Original formalization by Karim Abdel Sadek, Mark Bedaywi
-/

/-! ## Expert Setting

We fix N experts and T rounds. At each round t, the adversary reveals
a loss vector ℓ_t : Fin N → [0,1]. The learner picks a distribution
over experts and incurs the expected loss.

The code represents the whole realized trajectory as `LossSeq N T`.  This is
the right level of abstraction for the algebraic Hedge proof: each round only
uses the current loss vector and the weights computed from previous losses.
-/

/-- Loss at round t for expert i. Values in [0,1]. -/
-- The `[0, 1]` condition is kept as a separate predicate instead of being built
-- into the type, which keeps the algebraic definitions simple.
def LossSeq (N T : ℕ) := Fin T → Fin N → ℝ

/-- A loss sequence is valid if all losses lie in [0,1]. -/
def LossSeq.Valid {N T : ℕ} (ℓ : LossSeq N T) : Prop :=
  ∀ t i, 0 ≤ ℓ t i ∧ ℓ t i ≤ 1

/-! ## Hedge Algorithm

The Hedge algorithm maintains weights w_t(i) = exp(-η · L_t(i))
where L_t(i) = ∑_{s<t} ℓ_s(i) is the cumulative loss of expert i
through round t. The distribution at round t is obtained by normalizing
these weights.

The variable `t` in `cumLoss`, `hedgeWeight`, `potential`, and `hedgeDist` is a
natural number.  This makes prefixes like `0`, `t`, `t + 1`, and the final
horizon `T` easy to talk about, while actual round losses still use `Fin T`.
-/

/-- Cumulative loss of expert i through the first t rounds. -/
-- This sums exactly the rounds whose index is less than `t`.
noncomputable def cumLoss {N T : ℕ} (ℓ : LossSeq N T) (t : ℕ) (i : Fin N) : ℝ :=
  ((Finset.univ (α := Fin T)).filter (fun s => s.val < t)).sum (fun s => ℓ s i)

/-- Unnormalized weight of expert i at round t. -/
-- Experts with smaller cumulative loss get larger exponential weight.
noncomputable def hedgeWeight {N T : ℕ} (η : ℝ) (ℓ : LossSeq N T) (t : ℕ) (i : Fin N) : ℝ :=
  Real.exp (-η * cumLoss ℓ t i)

/-- Sum of unnormalized weights at round t (the potential). -/
-- The potential is the object we track.  Its one-step upper bound gives Hedge's
-- cumulative loss, while its final lower bound sees the best expert.
noncomputable def potential {N T : ℕ} (η : ℝ) (ℓ : LossSeq N T) (t : ℕ) : ℝ :=
  ∑ i : Fin N, hedgeWeight η ℓ t i

/-- The Hedge distribution at round t: normalized weights. -/
noncomputable def hedgeDist {N T : ℕ} (η : ℝ) (ℓ : LossSeq N T) (t : ℕ) (i : Fin N) : ℝ :=
  hedgeWeight η ℓ t i / potential η ℓ t

/-- Expected loss of the learner at round t under the Hedge distribution. -/
noncomputable def hedgeLoss {N T : ℕ} (η : ℝ) (ℓ : LossSeq N T) (t : Fin T) : ℝ :=
  ∑ i : Fin N, hedgeDist η ℓ t.val i * ℓ t i

/-- Cumulative loss of the Hedge algorithm over T rounds. -/
noncomputable def hedgeCumLoss {N T : ℕ} (η : ℝ) (ℓ : LossSeq N T) : ℝ :=
  ∑ t : Fin T, hedgeLoss η ℓ t

/-- Cumulative loss of the best expert in hindsight. -/
-- This is an infimum over a finite nonempty set of experts, so later we can
-- choose an expert attaining it when lower-bounding the final potential.
noncomputable def bestExpertLoss {N T : ℕ} (ℓ : LossSeq N T) : ℝ :=
  ⨅ i : Fin N, cumLoss ℓ T i

/-- Regret: difference between Hedge's cumulative loss and the best expert's. -/
noncomputable def regret {N T : ℕ} (η : ℝ) (ℓ : LossSeq N T) : ℝ :=
  hedgeCumLoss η ℓ - bestExpertLoss ℓ

/-! ## Key Lemmas -/

/-!
The lemmas in this section are the mechanics of the potential proof.  The main
work is to relate `W_{t+1} / W_t` to the current expected loss, then telescope
the resulting logarithmic inequality over all rounds.
-/

/-- The potential at time 0 equals N (all weights are 1). -/
private lemma potential_zero_aux_hfilt {N T : Nat} [inst : NeZero N] (ℓ : LossSeq N T) (i : Fin N) : ((Finset.univ (α := Fin T)).filter (fun s => s.val < 0)).sum (fun s => ℓ s i) = 0 := by
  apply Finset.sum_eq_zero
  intro s hs
  simp [Finset.mem_filter] at hs

lemma potential_zero {N T : ℕ} [NeZero N] (η : ℝ) (ℓ : LossSeq N T) :
    potential η ℓ 0 = N := by
  simp only [potential, hedgeWeight, cumLoss]
  let hfilt : ∀ i : Fin N, ((Finset.univ (α := Fin T)).filter (fun s => s.val < 0)).sum (fun s => ℓ s i) = 0 := (potential_zero_aux_hfilt ℓ)
  simp only [hfilt, mul_zero, neg_zero, exp_zero, Finset.sum_const, Finset.card_fin]
  simp

/-- Weights are always positive. -/
lemma hedgeWeight_pos {N T : ℕ} (η : ℝ) (ℓ : LossSeq N T) (t : ℕ) (i : Fin N) :
    0 < hedgeWeight η ℓ t i := by
  exact exp_pos _

/-- The potential is always positive. -/
lemma potential_pos {N T : ℕ} [NeZero N] (η : ℝ) (ℓ : LossSeq N T) (t : ℕ) :
    0 < potential η ℓ t := by
  apply Finset.sum_pos
  · intro i _
    exact hedgeWeight_pos η ℓ t i
  · exact Finset.univ_nonempty

/-- Hoeffding's inequality for the exponential:
    For x ∈ [0,1] and η > 0, exp(-ηx) ≤ 1 - (1 - exp(-η))x.
    Equivalently, exp(-ηx) ≤ 1 - ηx + η²x²/2 when η ∈ (0,1]. -/
private lemma exp_neg_le_linear_aux_h1x {x : ℝ} (hx1 : x ≤ 1) : 0 ≤ 1 - x :=
  sub_nonneg.mpr hx1

private lemma exp_neg_le_linear_aux_hconv {η x : ℝ} (hη : 0 < η) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (h1x : 0 ≤ 1 - x) : rexp (x • -η + (1 - x) • 0) ≤ x • rexp (-η) + (1 - x) • rexp 0 :=
  convexOn_exp.2 (Set.mem_univ (-η)) (Set.mem_univ 0) hx0 h1x
    (by linarith : x + (1 - x) = 1)

private lemma exp_neg_le_linear_aux_h_anon_1 {η x : ℝ} : x * -η = -η * x := by
  ring

lemma exp_neg_le_linear {η x : ℝ} (hη : 0 < η) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp (-η * x) ≤ 1 - (1 - Real.exp (-η)) * x := by
  -- Convexity: exp(x·a + (1-x)·b) ≤ x·exp(a) + (1-x)·exp(b)
  -- Apply with a = -η, b = 0.
  let hconv : rexp (x • -η + (1 - x) • 0) ≤ x • rexp (-η) + (1 - x) • rexp 0 := (exp_neg_le_linear_aux_hconv hη hx0 hx1 (exp_neg_le_linear_aux_h1x hx1))
  simp only [smul_eq_mul, mul_zero, add_zero, exp_zero, mul_one] at hconv
  -- hconv : exp (x * -η) ≤ x * exp (-η) + (1 - x)
  -- Goal : exp (-η * x) ≤ 1 - (1 - exp (-η)) * x
  -- These are equal since x * -η = -η * x and x * exp(-η) + 1 - x = 1 - (1 - exp(-η)) * x
  rw [(exp_neg_le_linear_aux_h_anon_1)] at hconv
  linarith

/-- Cumulative loss splits: L_{t+1}(i) = L_t(i) + ℓ_t(i). -/
private lemma cumLoss_succ_aux_h_anon_1 {T : Nat} (t : Fin T) : (Finset.univ (α := Fin T)).filter (fun s => s.val < t.val + 1) = ((Finset.univ).filter (fun s => s.val < t.val)) ∪ {t} := by
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

lemma cumLoss_succ {N T : ℕ} (ℓ : LossSeq N T) (t : Fin T) (i : Fin N) :
    cumLoss ℓ (t.val + 1) i = cumLoss ℓ t.val i + ℓ t i := by
  simp only [cumLoss]
  -- The prefix `{s | s < t+1}` is the old prefix `{s | s < t}` plus the
  -- current round `t`.
  let h_anon_1 : (Finset.univ (α := Fin T)).filter (fun s => s.val < t.val + 1) = ((Finset.univ).filter (fun s => s.val < t.val)) ∪ {t} := (cumLoss_succ_aux_h_anon_1 t)
  rw [h_anon_1, Finset.sum_union]
  · simp
  · simp [Finset.disjoint_left]
    intro s hs
    omega

/-- At the final horizon, cumulative loss is the sum over all rounds. -/
lemma cumLoss_horizon {N T : ℕ} (ℓ : LossSeq N T) (i : Fin N) :
    cumLoss ℓ T i = ∑ t : Fin T, ℓ t i := by
  simp only [cumLoss]
  congr 1
  ext t
  simp [t.isLt]

/-- The weight factorizes: w_{t+1}(i) = w_t(i) · exp(-η · ℓ_t(i)). -/
lemma hedgeWeight_succ {N T : ℕ} (η : ℝ) (ℓ : LossSeq N T) (t : Fin T) (i : Fin N) :
    hedgeWeight η ℓ (t.val + 1) i = hedgeWeight η ℓ t.val i * Real.exp (-η * ℓ t i) := by
  simp only [hedgeWeight, cumLoss_succ]
  ring_nf
  rw [← exp_add]
  ring_nf

/-- The Hedge distribution sums to 1. -/
lemma hedgeDist_sum {N T : ℕ} [NeZero N] (η : ℝ) (ℓ : LossSeq N T) (t : ℕ) :
    ∑ i : Fin N, hedgeDist η ℓ t i = 1 := by
  -- Normalization by the positive potential turns weights into a probability
  -- distribution.
  simp only [hedgeDist]
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (potential_pos η ℓ t))

/-- Key potential ratio lemma (Cesa-Bianchi & Lugosi, Lemma 2.2):
    W_{t+1} / W_t ≤ 1 - (1 - exp(-η)) · ℓ_t · p_t
    where ℓ_t · p_t is the expected loss at round t. -/
private lemma potential_ratio_le_aux_hWt {N T : Nat} [inst : NeZero N] (η : ℝ) (hη : 0 < η) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (t : Fin T) (ht : ↑t + 1 ≤ T) : 0 < potential η ℓ ↑t :=
  potential_pos η ℓ t.val

private lemma potential_ratio_le_aux_hW_succ {N T : Nat} [inst : NeZero N] (η : ℝ) (hη : 0 < η) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (t : Fin T) (ht : ↑t + 1 ≤ T) (hWt : 0 < potential η ℓ ↑t) : potential η ℓ (t.val + 1) = ∑ i : Fin N, hedgeWeight η ℓ t.val i * Real.exp (-η * ℓ t i) := by
  simp only [potential]; congr 1; ext i; exact hedgeWeight_succ η ℓ t i

private lemma potential_ratio_le_aux_hbound {N T : Nat} [inst : NeZero N] (η : ℝ) (hη : 0 < η) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (t : Fin T) (ht : ↑t + 1 ≤ T) (hWt : 0 < potential η ℓ ↑t) (hW_succ : potential η ℓ (t.val + 1) = ∑ i : Fin N, hedgeWeight η ℓ t.val i * Real.exp (-η * ℓ t i)) (i : Fin N) : hedgeWeight η ℓ t.val i * Real.exp (-η * ℓ t i) ≤ hedgeWeight η ℓ t.val i * (1 - (1 - Real.exp (-η)) * ℓ t i) := by
  exact mul_le_mul_of_nonneg_left (exp_neg_le_linear hη (hℓ t i).1 (hℓ t i).2)
    (hedgeWeight_pos η ℓ t.val i).le

private lemma potential_ratio_le_aux_hW_ne {N T : Nat} [inst : NeZero N] (η : ℝ) (hη : 0 < η) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (t : Fin T) (ht : ↑t + 1 ≤ T) (hW_succ : potential η ℓ (t.val + 1) = ∑ i : Fin N, hedgeWeight η ℓ t.val i * Real.exp (-η * ℓ t i)) (c : ℝ) (hbound : ∀ i : Fin N, hedgeWeight η ℓ t.val i * Real.exp (-η * ℓ t i) ≤ hedgeWeight η ℓ t.val i * (1 - (1 - Real.exp (-η)) * ℓ t i)) (hc_def : c = 1 - rexp (-η)) (W : ℝ) (hWt : 0 < potential η ℓ ↑t) (hW_def : W = potential η ℓ ↑t) : potential η ℓ ↑t ≠ 0 :=
  ne_of_gt hWt

private lemma potential_ratio_le_aux_hHL {N T : Nat} [inst : NeZero N] (η : ℝ) (hη : 0 < η) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (t : Fin T) (ht : ↑t + 1 ≤ T) (hW_succ : potential η ℓ (t.val + 1) = ∑ i : Fin N, hedgeWeight η ℓ t.val i * Real.exp (-η * ℓ t i)) (c : ℝ) (hbound : ∀ i : Fin N, hedgeWeight η ℓ t.val i * Real.exp (-η * ℓ t i) ≤ hedgeWeight η ℓ t.val i * (1 - (1 - Real.exp (-η)) * ℓ t i)) (hc_def : c = 1 - rexp (-η)) (W : ℝ) (hWt : 0 < potential η ℓ ↑t) (hW_def : W = potential η ℓ ↑t) (hW_ne : potential η ℓ ↑t ≠ 0) : hedgeLoss η ℓ t = (∑ i : Fin N, hedgeWeight η ℓ t.val i * ℓ t i) / W := by
  simp only [hedgeLoss, hedgeDist, hW_def, Finset.sum_div]
  congr 1; ext i; ring

private lemma potential_ratio_le_aux_step1 {N T : Nat} [inst : NeZero N] (η : Real) (hη : LT.lt 0 η) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (t : Fin T) (ht : LE.le (HAdd.hAdd (↑t) 1) T) (hW_succ :
    Eq (potential η ℓ (HAdd.hAdd (↑t) 1))
      (Finset.univ.sum fun (i : Fin N) =>
        HMul.hMul (hedgeWeight η ℓ (↑t) i) (Real.exp (HMul.hMul (Neg.neg η) (ℓ t i))))) (c : Real) (hbound :
    ∀ (i : Fin N),
      LE.le (HMul.hMul (hedgeWeight η ℓ (↑t) i) (Real.exp (HMul.hMul (Neg.neg η) (ℓ t i))))
        (HMul.hMul (hedgeWeight η ℓ (↑t) i) (HSub.hSub 1 (HMul.hMul c (ℓ t i))))) (hc_def : Eq c (HSub.hSub 1 (Real.exp (Neg.neg η)))) (W : Real) (hWt : 0 < potential η ℓ ↑t) (hW_def : Eq W (potential η ℓ ↑t)) (hW_ne : Ne (potential η ℓ ↑t) 0) (hHL :
    Eq (hedgeLoss η ℓ t) (HDiv.hDiv (Finset.univ.sum fun (i : Fin N) => HMul.hMul (hedgeWeight η ℓ (↑t) i) (ℓ t i)) W)) : LE.le (Finset.univ.sum fun (i : Fin N) => HMul.hMul (hedgeWeight η ℓ (↑t) i) (Real.exp (HMul.hMul (Neg.neg η) (ℓ t i)))) (Finset.univ.sum fun (i : Fin N) => HMul.hMul (hedgeWeight η ℓ (↑t) i) (HSub.hSub 1 (HMul.hMul c (ℓ t i)))) :=
  Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hbound i

private lemma potential_ratio_le_aux_hW_ne__dup2 {N T : Nat} [inst : NeZero N] (η : ℝ) (hη : 0 < η) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (t : Fin T) (ht : ↑t + 1 ≤ T) (hW_succ : potential η ℓ (t.val + 1) = ∑ i : Fin N, hedgeWeight η ℓ t.val i * Real.exp (-η * ℓ t i)) (c : ℝ) (hbound : ∀ i : Fin N, hedgeWeight η ℓ t.val i * Real.exp (-η * ℓ t i) ≤ hedgeWeight η ℓ t.val i * (1 - (1 - Real.exp (-η)) * ℓ t i)) (hc_def : c = 1 - rexp (-η)) (W : ℝ) (hWt : 0 < potential η ℓ ↑t) (hW_def : W = potential η ℓ ↑t) (hW_ne : potential η ℓ ↑t ≠ 0) (hHL : hedgeLoss η ℓ t = (∑ i : Fin N, hedgeWeight η ℓ t.val i * ℓ t i) / W) (step1 : LE.le (Finset.univ.sum fun (i : Fin N) => HMul.hMul (hedgeWeight η ℓ (↑t) i) (Real.exp (HMul.hMul (Neg.neg η) (ℓ t i)))) (Finset.univ.sum fun (i : Fin N) => HMul.hMul (hedgeWeight η ℓ (↑t) i) (HSub.hSub 1 (HMul.hMul c (ℓ t i))))) : (∑ i : Fin N, hedgeWeight η ℓ t.val i) ≠ 0 :=
  ne_of_gt hWt

private lemma potential_ratio_le_aux_h_anon_1 {N T : Nat} [inst : NeZero N] (η : ℝ) (hη : 0 < η) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (t : Fin T) (ht : ↑t + 1 ≤ T) (hW_succ : potential η ℓ (t.val + 1) = ∑ i : Fin N, hedgeWeight η ℓ t.val i * Real.exp (-η * ℓ t i)) (c : ℝ) (hbound : ∀ i : Fin N, hedgeWeight η ℓ t.val i * Real.exp (-η * ℓ t i) ≤ hedgeWeight η ℓ t.val i * (1 - (1 - Real.exp (-η)) * ℓ t i)) (hc_def : c = 1 - rexp (-η)) (W : ℝ) (hWt : 0 < potential η ℓ ↑t) (hW_def : W = potential η ℓ ↑t) (hW_ne : potential η ℓ ↑t ≠ 0) (hHL : hedgeLoss η ℓ t = (∑ i : Fin N, hedgeWeight η ℓ t.val i * ℓ t i) / W) (step1 : LE.le (Finset.univ.sum fun (i : Fin N) => HMul.hMul (hedgeWeight η ℓ (↑t) i) (Real.exp (HMul.hMul (Neg.neg η) (ℓ t i)))) (Finset.univ.sum fun (i : Fin N) => HMul.hMul (hedgeWeight η ℓ (↑t) i) (HSub.hSub 1 (HMul.hMul c (ℓ t i))))) (hW_ne__dup2 : (∑ i : Fin N, hedgeWeight η ℓ t.val i) ≠ 0) (i : Fin N) : hedgeWeight η ℓ t.val i * (1 - c * ℓ t i) = hedgeWeight η ℓ t.val i - c * (hedgeWeight η ℓ t.val i * ℓ t i) := by
  ring

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

  -- Rewrite W_{t+1}/W_t = ∑ p_t(i) · exp(-η · ℓ_t(i))
  -- Step 1: Rewrite potential ratio using weight factorization
  rw [div_le_iff₀ ((potential_ratio_le_aux_hWt η hη ℓ hℓ t ht))]
  -- Goal: potential η ℓ (t+1) ≤ (1 - (1 - exp(-η)) * hedgeLoss η ℓ t) * potential η ℓ t
  -- W_{t+1} = ∑ w_t(i) * exp(-η * ℓ_t(i))
  let hW_succ : potential η ℓ (t.val + 1) = ∑ i : Fin N, hedgeWeight η ℓ t.val i * Real.exp (-η * ℓ t i) := (potential_ratio_le_aux_hW_succ η hη ℓ hℓ t ht ((potential_ratio_le_aux_hWt η hη ℓ hℓ t ht)))
  rw [hW_succ]
  -- Step 2: Apply exp_neg_le_linear to each term
  let hbound : ∀ i : Fin N, hedgeWeight η ℓ t.val i * Real.exp (-η * ℓ t i) ≤ hedgeWeight η ℓ t.val i * (1 - (1 - Real.exp (-η)) * ℓ t i) := (potential_ratio_le_aux_hbound η hη ℓ hℓ t ht ((potential_ratio_le_aux_hWt η hη ℓ hℓ t ht)) hW_succ)
  -- Step 3: Sum up the bounds and show RHS = (1 - c * hedgeLoss) * W
  -- where c = 1 - exp(-η) and W = potential.
  -- RHS expanded: W - c * W * hedgeLoss = W - c * ∑(w_i * ℓ_i / W) * W = W - c * ∑ w_i * ℓ_i
  -- LHS ≤ ∑ w_i * (1 - c * ℓ_i) = ∑ w_i - c * ∑ w_i * ℓ_i = W - c * ∑ w_i * ℓ_i = RHS ✓
  set c := (1 : ℝ) - Real.exp (-η) with hc_def
  set W := potential η ℓ t.val with hW_def
  -- Expand the RHS
  let hW_ne : potential η ℓ ↑t ≠ 0 := (potential_ratio_le_aux_hW_ne η hη ℓ hℓ t ht hW_succ c hbound hc_def W ((potential_ratio_le_aux_hWt η hη ℓ hℓ t ht)) hW_def)
  -- hedgeLoss = (∑ w_i * ℓ_i) / W
  let hHL : hedgeLoss η ℓ t = (∑ i : Fin N, hedgeWeight η ℓ t.val i * ℓ t i) / W := (potential_ratio_le_aux_hHL η hη ℓ hℓ t ht hW_succ c hbound hc_def W ((potential_ratio_le_aux_hWt η hη ℓ hℓ t ht)) hW_def hW_ne)
  -- Goal: ∑ w_i * exp(-η * ℓ_i) ≤ (1 - c * hedgeLoss) * W
  -- ≤ ∑ w_i * (1 - c * ℓ_i) (from hbound)
  -- = ∑ w_i - c * ∑ w_i * ℓ_i
  -- = W - c * hedgeLoss * W = (1 - c * hedgeLoss) * W ✓
  let step1 : LE.le (Finset.univ.sum fun (i : Fin N) => HMul.hMul (hedgeWeight η ℓ (↑t) i) (Real.exp (HMul.hMul (Neg.neg η) (ℓ t i)))) (Finset.univ.sum fun (i : Fin N) => HMul.hMul (hedgeWeight η ℓ (↑t) i) (HSub.hSub 1 (HMul.hMul c (ℓ t i)))) := (potential_ratio_le_aux_step1 η hη ℓ hℓ t ht hW_succ c hbound hc_def W ((potential_ratio_le_aux_hWt η hη ℓ hℓ t ht)) hW_def hW_ne hHL)
  suffices ∑ i, hedgeWeight η ℓ t.val i * (1 - c * ℓ t i) =
      (1 - c * hedgeLoss η ℓ t) * W by linarith [hW_succ]
  rw [hHL, hW_def, potential]
  let hW_ne__dup2 : (∑ i : Fin N, hedgeWeight η ℓ t.val i) ≠ 0 := (potential_ratio_le_aux_hW_ne__dup2 η hη ℓ hℓ t ht hW_succ c hbound hc_def W ((potential_ratio_le_aux_hWt η hη ℓ hℓ t ht)) hW_def hW_ne hHL step1)

  simp_rw [((potential_ratio_le_aux_h_anon_1 η hη ℓ hℓ t ht hW_succ c hbound hc_def W ((potential_ratio_le_aux_hWt η hη ℓ hℓ t ht)) hW_def hW_ne hHL step1 hW_ne__dup2)), Finset.sum_sub_distrib, ← Finset.mul_sum]
  field_simp

/-- Logarithmic potential inequality:
    Using ln(1 - x) ≤ -x and the potential ratio,
    ln W_{t+1} - ln W_t ≤ -(1 - exp(-η)) · ℓ_t · p_t. -/
private lemma log_potential_step_aux_hWt {N T : Nat} [inst : NeZero N] (η : ℝ) (hη : 0 < η) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (t : Fin T) (ht : ↑t + 1 ≤ T) : 0 < potential η ℓ ↑t :=
  potential_pos η ℓ t.val

private lemma log_potential_step_aux_hWt1 {N T : Nat} [inst : NeZero N] (η : ℝ) (hη : 0 < η) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (t : Fin T) (ht : ↑t + 1 ≤ T) (hWt : 0 < potential η ℓ ↑t) : 0 < potential η ℓ (↑t + 1) :=
  potential_pos η ℓ (t.val + 1)

private lemma log_potential_step_aux_hratio {N T : Nat} [inst : NeZero N] (η : ℝ) (hη : 0 < η) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (t : Fin T) (ht : ↑t + 1 ≤ T) (hWt : 0 < potential η ℓ ↑t) (hWt1 : 0 < potential η ℓ (↑t + 1)) : potential η ℓ (↑t + 1) / potential η ℓ ↑t ≤ 1 - (1 - rexp (-η)) * hedgeLoss η ℓ t :=
  potential_ratio_le η hη ℓ hℓ t ht

private lemma log_potential_step_aux_hratio_pos {N T : Nat} [inst : NeZero N] (η : ℝ) (hη : 0 < η) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (t : Fin T) (ht : ↑t + 1 ≤ T) (hWt : 0 < potential η ℓ ↑t) (hWt1 : 0 < potential η ℓ (↑t + 1)) (c : ℝ) (hratio : potential η ℓ (↑t + 1) / potential η ℓ ↑t ≤ 1 - (1 - rexp (-η)) * hedgeLoss η ℓ t) : 0 < potential η ℓ (t.val + 1) / potential η ℓ t.val :=
  div_pos hWt1 hWt

private lemma log_potential_step_aux_h1mc_pos {N T : Nat} [inst : NeZero N] (η : ℝ) (hη : 0 < η) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (t : Fin T) (ht : ↑t + 1 ≤ T) (hWt : 0 < potential η ℓ ↑t) (hWt1 : 0 < potential η ℓ (↑t + 1)) (c : ℝ) (hratio : potential η ℓ (↑t + 1) / potential η ℓ ↑t ≤ 1 - (1 - rexp (-η)) * hedgeLoss η ℓ t) (hratio_pos : 0 < potential η ℓ (t.val + 1) / potential η ℓ t.val) : 0 < 1 - (1 - rexp (-η)) * hedgeLoss η ℓ t := by
  linarith

lemma log_potential_step {N T : ℕ} [NeZero N] (η : ℝ) (hη : 0 < η)
    (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (t : Fin T) (ht : t.val + 1 ≤ T) :
    Real.log (potential η ℓ (t.val + 1)) - Real.log (potential η ℓ t.val)
      ≤ -(1 - Real.exp (-η)) * hedgeLoss η ℓ t := by
  -- Convert the multiplicative potential-ratio bound into an additive
  -- log-potential bound.  This is what will telescope across time.
  let hWt : 0 < potential η ℓ ↑t := (log_potential_step_aux_hWt η hη ℓ hℓ t ht)

  rw [← Real.log_div (ne_of_gt ((log_potential_step_aux_hWt1 η hη ℓ hℓ t ht hWt))) (ne_of_gt hWt)]
  let hratio : potential η ℓ (↑t + 1) / potential η ℓ ↑t ≤ 1 - (1 - rexp (-η)) * hedgeLoss η ℓ t := (log_potential_step_aux_hratio η hη ℓ hℓ t ht hWt ((log_potential_step_aux_hWt1 η hη ℓ hℓ t ht hWt)))
  set c := (1 : ℝ) - Real.exp (-η)
  -- The ratio is positive (from hratio and the fact W_{t+1}/W_t > 0)


  -- log(ratio) ≤ log(1 - c * hedgeLoss) ≤ (1 - c * hedgeLoss) - 1 = -c * hedgeLoss
  -- using log x ≤ x - 1 for x > 0.
  calc Real.log (potential η ℓ (t.val + 1) / potential η ℓ t.val)
      ≤ Real.log (1 - c * hedgeLoss η ℓ t) := by
        exact Real.log_le_log ((log_potential_step_aux_hratio_pos η hη ℓ hℓ t ht hWt ((log_potential_step_aux_hWt1 η hη ℓ hℓ t ht hWt)) c hratio)) hratio
    _ ≤ (1 - c * hedgeLoss η ℓ t) - 1 := Real.log_le_sub_one_of_pos ((log_potential_step_aux_h1mc_pos η hη ℓ hℓ t ht hWt ((log_potential_step_aux_hWt1 η hη ℓ hℓ t ht hWt)) c hratio ((log_potential_step_aux_hratio_pos η hη ℓ hℓ t ht hWt ((log_potential_step_aux_hWt1 η hη ℓ hℓ t ht hWt)) c hratio))))
    _ = -(1 - Real.exp (-η)) * hedgeLoss η ℓ t := by ring

/-- The 1 - exp(-η) approximation: for η > 0,
    1 - exp(-η) ≥ η - η²/2. -/
-- Helper: exp(-t) ≤ 1 - t + t²/2 for t ≥ 0.
-- Proof: ⟺ 1 ≤ exp(t) · (1 - t + t²/2) (multiply by exp(t) > 0).
-- From quadratic_le_exp_of_nonneg: 1 + t + t²/2 ≤ exp(t).
-- Then exp(t) · (1 - t + t²/2) ≥ (1 + t + t²/2)(1 - t + t²/2) = (1 + t²/2)² - t² = 1 + t⁴/4 ≥ 1.
private lemma exp_neg_le_quadratic_aux_he {t : ℝ} : (0 : ℝ) < Real.exp t :=
  exp_pos t

private lemma exp_neg_le_quadratic_aux_hq {t : ℝ} (ht : 0 ≤ t) : (0 : ℝ) < 1 - t + t ^ 2 / 2 := by
  nlinarith [sq_nonneg t]

private lemma exp_neg_le_quadratic_aux_hquad {t : ℝ} (ht : 0 ≤ t) (he : (0 : ℝ) < Real.exp t) (hq : (0 : ℝ) < 1 - t + t ^ 2 / 2) : 1 + t + t ^ 2 / 2 ≤ rexp t :=
  quadratic_le_exp_of_nonneg ht

private lemma exp_neg_le_quadratic_aux_h_anon_1 {t : ℝ} : (1 + t + t ^ 2 / 2) * (1 - t + t ^ 2 / 2) = 1 + t ^ 4 / 4 := by
  ring

private lemma exp_neg_le_quadratic_aux_key {t : ℝ} (hq : (0 : ℝ) < 1 - t + t ^ 2 / 2) (hquad : 1 + t + t ^ 2 / 2 ≤ rexp t) : 1 ≤ Real.exp t * (1 - t + t ^ 2 / 2) := by
  let h_anon_1 : (1 + t + t ^ 2 / 2) * (1 - t + t ^ 2 / 2) = 1 + t ^ 4 / 4 := exp_neg_le_quadratic_aux_h_anon_1
  nlinarith [sq_nonneg (t ^ 2), mul_le_mul_of_nonneg_right hquad hq.le]

lemma exp_neg_le_quadratic {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-t) ≤ 1 - t + t ^ 2 / 2 := by
  -- We prove the bound by multiplying both sides by `exp t > 0` and using the
  -- standard lower Taylor bound for `exp t`.
  let he : (0 : ℝ) < Real.exp t := exp_neg_le_quadratic_aux_he

  -- exp(t) ≥ 1 + t + t²/2

  -- (1 + t + t²/2)(1 - t + t²/2) = 1 + t⁴/4 ≥ 1
  -- So exp(t) * (1 - t + t²/2) ≥ (1 + t + t²/2)(1 - t + t²/2) ≥ 1
  let key : 1 ≤ Real.exp t * (1 - t + t ^ 2 / 2) := (exp_neg_le_quadratic_aux_key ((exp_neg_le_quadratic_aux_hq ht)) ((exp_neg_le_quadratic_aux_hquad ht he ((exp_neg_le_quadratic_aux_hq ht)))))
  -- exp(-t) = (exp t)⁻¹ ≤ 1 - t + t²/2
  rw [exp_neg]
  exact le_of_mul_le_mul_left (by nlinarith [mul_inv_cancel₀ he.ne']) he

private lemma one_sub_exp_neg_ge_aux_h {η : ℝ} (hη : 0 < η) : rexp (-η) ≤ 1 - η + η ^ 2 / 2 :=
  exp_neg_le_quadratic hη.le

lemma one_sub_exp_neg_ge {η : ℝ} (hη : 0 < η) :
    1 - Real.exp (-η) ≥ η - η ^ 2 / 2 := by
  -- Rearranged form of the previous quadratic upper bound on `exp (-η)`.
  let h : rexp (-η) ≤ 1 - η + η ^ 2 / 2 := (one_sub_exp_neg_ge_aux_h hη)
  linarith

/-- Lower bound on the final potential using the best expert:
    W_T ≥ max_i w_T(i) = exp(-η · min_i L_T(i)). -/
private lemma potential_ge_best_expert_aux_hinf {N T : Nat} [inst : NeZero N] (ℓ : LossSeq N T) (i₀ : Fin N) (hi₀ : ∀ (x : Fin N), cumLoss ℓ T i₀ ≤ cumLoss ℓ T x) : ⨅ i, cumLoss ℓ T i = cumLoss ℓ T i₀ :=
  le_antisymm (ciInf_le ⟨_, by rintro _ ⟨j, rfl⟩; exact hi₀ j⟩ i₀) (le_ciInf hi₀)

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
  rw [(potential_ge_best_expert_aux_hinf ℓ i₀ hi₀)]
  -- Goal: exp(-η * cumLoss i₀) ≤ ∑ exp(-η * cumLoss i)
  exact Finset.single_le_sum (f := fun i => Real.exp (-η * cumLoss ℓ T i))
    (fun i _ => (exp_pos _).le) (Finset.mem_univ i₀)

/-- The hedgeDist is nonneg. -/
lemma hedgeDist_nonneg {N T : ℕ} [NeZero N] (η : ℝ) (ℓ : LossSeq N T) (t : ℕ) (i : Fin N) :
    0 ≤ hedgeDist η ℓ t i :=
  div_nonneg (hedgeWeight_pos η ℓ t i).le (potential_pos η ℓ t).le

/-- The expected loss at each round is at most 1 for valid losses. -/
private lemma hedgeLoss_le_one_aux_hsum {N T : Nat} [inst : NeZero N] (η : ℝ) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (t : Fin T) : hedgeLoss η ℓ t ≤ ∑ i : Fin N, hedgeDist η ℓ t.val i * 1 := by
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left (hℓ t i).2 (hedgeDist_nonneg η ℓ t.val i)

lemma hedgeLoss_le_one {N T : ℕ} [NeZero N] (η : ℝ) (ℓ : LossSeq N T) (hℓ : ℓ.Valid)
    (t : Fin T) : hedgeLoss η ℓ t ≤ 1 := by
  -- A convex combination of losses in `[0, 1]` is at most `1`.
  let hsum : hedgeLoss η ℓ t ≤ ∑ i : Fin N, hedgeDist η ℓ t.val i * 1 := (hedgeLoss_le_one_aux_hsum η ℓ hℓ t)
  simp only [mul_one] at hsum
  linarith [hedgeDist_sum η ℓ t.val]

/-- The expected loss at each round is nonneg for valid losses. -/
lemma hedgeLoss_nonneg {N T : ℕ} [NeZero N] (η : ℝ) (ℓ : LossSeq N T) (hℓ : ℓ.Valid)
    (t : Fin T) : 0 ≤ hedgeLoss η ℓ t := by
  -- A convex combination of nonnegative losses is nonnegative.
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (hedgeDist_nonneg η ℓ t.val i) (hℓ t i).1

/-! ## Main Theorem -/

/-- **Hedge Regret Bound** (Cesa-Bianchi & Lugosi, Theorem 2.2):
    For any valid loss sequence with N experts, T rounds, and η ∈ (0,1],
    the regret of Hedge is at most (ln N)/η + ηT/2. -/
private lemma hedge_regret_bound_aux_hstep {N T : Nat} [inst : NeZero N] (η : ℝ) (hη_pos : 0 < η) (hη_le : η ≤ 1) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (t : Fin T) : Real.log (potential η ℓ (t.val + 1)) - Real.log (potential η ℓ t.val) ≤ -(1 - Real.exp (-η)) * hedgeLoss η ℓ t :=
  log_potential_step η hη_pos ℓ hℓ t (by omega)

private lemma hedge_regret_bound_aux_h1 {N T : Nat} [inst : NeZero N] (η : ℝ) (hη_pos : 0 < η) (hη_le : η ≤ 1) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (hstep : ∀ t : Fin T, Real.log (potential η ℓ (t.val + 1)) - Real.log (potential η ℓ t.val) ≤ -(1 - Real.exp (-η)) * hedgeLoss η ℓ t) (t : Fin T) : log (potential η ℓ (↑t + 1)) - log (potential η ℓ ↑t) ≤ -(1 - rexp (-η)) * hedgeLoss η ℓ t :=
  hstep t

private lemma hedge_regret_bound_aux_hge {N T : Nat} [inst : NeZero N] (η : ℝ) (hη_pos : 0 < η) (hη_le : η ≤ 1) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (hstep : ∀ t : Fin T, Real.log (potential η ℓ (t.val + 1)) - Real.log (potential η ℓ t.val) ≤ -(1 - Real.exp (-η)) * hedgeLoss η ℓ t) (t : Fin T) (h1 : log (potential η ℓ (↑t + 1)) - log (potential η ℓ ↑t) ≤ -(1 - rexp (-η)) * hedgeLoss η ℓ t) : 1 - rexp (-η) ≥ η - η ^ 2 / 2 :=
  @one_sub_exp_neg_ge η hη_pos

private lemma hedge_regret_bound_aux_hle1 {N T : Nat} [inst : NeZero N] (η : ℝ) (hη_pos : 0 < η) (hη_le : η ≤ 1) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (hstep : ∀ t : Fin T, Real.log (potential η ℓ (t.val + 1)) - Real.log (potential η ℓ t.val) ≤ -(1 - Real.exp (-η)) * hedgeLoss η ℓ t) (t : Fin T) (h1 : log (potential η ℓ (↑t + 1)) - log (potential η ℓ ↑t) ≤ -(1 - rexp (-η)) * hedgeLoss η ℓ t) (hge : 1 - rexp (-η) ≥ η - η ^ 2 / 2) : hedgeLoss η ℓ t ≤ 1 :=
  hedgeLoss_le_one η ℓ hℓ t

private lemma hedge_regret_bound_aux_hnn {N T : Nat} [inst : NeZero N] (η : ℝ) (hη_pos : 0 < η) (hη_le : η ≤ 1) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (hstep : ∀ t : Fin T, Real.log (potential η ℓ (t.val + 1)) - Real.log (potential η ℓ t.val) ≤ -(1 - Real.exp (-η)) * hedgeLoss η ℓ t) (t : Fin T) (h1 : log (potential η ℓ (↑t + 1)) - log (potential η ℓ ↑t) ≤ -(1 - rexp (-η)) * hedgeLoss η ℓ t) (hge : 1 - rexp (-η) ≥ η - η ^ 2 / 2) (hle1 : hedgeLoss η ℓ t ≤ 1) : 0 ≤ hedgeLoss η ℓ t :=
  hedgeLoss_nonneg η ℓ hℓ t

private lemma hedge_regret_bound_aux_hrelax {N T : Nat} [inst : NeZero N] (η : ℝ) (hη_pos : 0 < η) (hη_le : η ≤ 1) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (hstep : ∀ t : Fin T, Real.log (potential η ℓ (t.val + 1)) - Real.log (potential η ℓ t.val) ≤ -(1 - Real.exp (-η)) * hedgeLoss η ℓ t) (t : Fin T) : Real.log (potential η ℓ (t.val + 1)) - Real.log (potential η ℓ t.val) ≤ -η * hedgeLoss η ℓ t + η ^ 2 / 2 := by
  let h1 : log (potential η ℓ (↑t + 1)) - log (potential η ℓ ↑t) ≤ -(1 - rexp (-η)) * hedgeLoss η ℓ t := (hedge_regret_bound_aux_h1 η hη_pos hη_le ℓ hℓ hstep t)
  let hge : 1 - rexp (-η) ≥ η - η ^ 2 / 2 := (hedge_regret_bound_aux_hge η hη_pos hη_le ℓ hℓ hstep t h1)
  let hle1 : hedgeLoss η ℓ t ≤ 1 := (hedge_regret_bound_aux_hle1 η hη_pos hη_le ℓ hℓ hstep t h1 hge)
  let hnn : 0 ≤ hedgeLoss η ℓ t := (hedge_regret_bound_aux_hnn η hη_pos hη_le ℓ hℓ hstep t h1 hge hle1)
  nlinarith [sq_nonneg η]

private lemma hedge_regret_bound_aux_hbounds {N T : Nat} [inst : NeZero N] (η : ℝ) (hη_pos : 0 < η) (hη_le : η ≤ 1) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (hstep : ∀ t : Fin T, Real.log (potential η ℓ (t.val + 1)) - Real.log (potential η ℓ t.val) ≤ -(1 - Real.exp (-η)) * hedgeLoss η ℓ t) (hrelax : ∀ t : Fin T, Real.log (potential η ℓ (t.val + 1)) - Real.log (potential η ℓ t.val) ≤ -η * hedgeLoss η ℓ t + η ^ 2 / 2) : ∑ i : Fin T, (log (potential η ℓ (↑i + 1)) - log (potential η ℓ ↑i)) ≤ ∑ i : Fin T, (-η * hedgeLoss η ℓ i + η ^ 2 / 2) :=
  Finset.sum_le_sum fun t (_ : t ∈ Finset.univ) => hrelax t

private lemma hedge_regret_bound_aux_hrhs {N T : Nat} [inst : NeZero N] (η : ℝ) (hη_pos : 0 < η) (hη_le : η ≤ 1) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (hstep : ∀ t : Fin T, Real.log (potential η ℓ (t.val + 1)) - Real.log (potential η ℓ t.val) ≤ -(1 - Real.exp (-η)) * hedgeLoss η ℓ t) (hrelax : ∀ t : Fin T, Real.log (potential η ℓ (t.val + 1)) - Real.log (potential η ℓ t.val) ≤ -η * hedgeLoss η ℓ t + η ^ 2 / 2) (hbounds : ∑ i : Fin T, (log (potential η ℓ (↑i + 1)) - log (potential η ℓ ↑i)) ≤ ∑ i : Fin T, (-η * hedgeLoss η ℓ i + η ^ 2 / 2)) : ∑ t : Fin T, (-η * hedgeLoss η ℓ t + η ^ 2 / 2) = -η * hedgeCumLoss η ℓ + η ^ 2 / 2 * T := by
  simp only [hedgeCumLoss, Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_fin]
  ring

private lemma hedge_regret_bound_aux_hsum {N T : Nat} [inst : NeZero N] (η : ℝ) (hη_pos : 0 < η) (hη_le : η ≤ 1) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (hstep : ∀ t : Fin T, Real.log (potential η ℓ (t.val + 1)) - Real.log (potential η ℓ t.val) ≤ -(1 - Real.exp (-η)) * hedgeLoss η ℓ t) (hrelax : ∀ t : Fin T, Real.log (potential η ℓ (t.val + 1)) - Real.log (potential η ℓ t.val) ≤ -η * hedgeLoss η ℓ t + η ^ 2 / 2) : Real.log (potential η ℓ T) - Real.log (potential η ℓ 0) ≤ -η * hedgeCumLoss η ℓ + η ^ 2 / 2 * T := by
  -- Sum the per-step bounds

  let hrhs : ∑ t : Fin T, (-η * hedgeLoss η ℓ t + η ^ 2 / 2) = -η * hedgeCumLoss η ℓ + η ^ 2 / 2 * T := (hedge_regret_bound_aux_hrhs η hη_pos hη_le ℓ hℓ hstep hrelax ((hedge_regret_bound_aux_hbounds η hη_pos hη_le ℓ hℓ hstep hrelax)))
  -- Telescoping: ∑ (f(t+1) - f(t)) = f(T) - f(0)
  suffices htel : ∑ t : Fin T,
      (Real.log (potential η ℓ (t.val + 1)) - Real.log (potential η ℓ t.val)) =
      Real.log (potential η ℓ T) - Real.log (potential η ℓ 0) by linarith [((hedge_regret_bound_aux_hbounds η hη_pos hη_le ℓ hℓ hstep hrelax))]
  set f := fun n => Real.log (potential η ℓ n)
  show ∑ t : Fin T, (f (t.val + 1) - f t.val) = f T - f 0
  conv_lhs => arg 2; ext t; rw [show t.val = (t : ℕ) from rfl]
  rw [Fin.sum_univ_eq_sum_range (fun n => f (n + 1) - f n)]
  exact Finset.sum_range_sub f T

private lemma hedge_regret_bound_aux_hW0 {N T : Nat} [inst : NeZero N] (η : ℝ) (hη_pos : 0 < η) (hη_le : η ≤ 1) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (hstep : ∀ t : Fin T, Real.log (potential η ℓ (t.val + 1)) - Real.log (potential η ℓ t.val) ≤ -(1 - Real.exp (-η)) * hedgeLoss η ℓ t) (hrelax : ∀ t : Fin T, Real.log (potential η ℓ (t.val + 1)) - Real.log (potential η ℓ t.val) ≤ -η * hedgeLoss η ℓ t + η ^ 2 / 2) (hsum : Real.log (potential η ℓ T) - Real.log (potential η ℓ 0) ≤ -η * hedgeCumLoss η ℓ + η ^ 2 / 2 * T) : Real.log (potential η ℓ 0) = Real.log N := by
  rw [potential_zero]

private lemma hedge_regret_bound_aux_hWT {N T : Nat} [inst : NeZero N] (η : ℝ) (hη_pos : 0 < η) (hη_le : η ≤ 1) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (hstep : ∀ t : Fin T, Real.log (potential η ℓ (t.val + 1)) - Real.log (potential η ℓ t.val) ≤ -(1 - Real.exp (-η)) * hedgeLoss η ℓ t) (hrelax : ∀ t : Fin T, Real.log (potential η ℓ (t.val + 1)) - Real.log (potential η ℓ t.val) ≤ -η * hedgeLoss η ℓ t + η ^ 2 / 2) (hsum : Real.log (potential η ℓ T) - Real.log (potential η ℓ 0) ≤ -η * hedgeCumLoss η ℓ + η ^ 2 / 2 * T) (hW0 : Real.log (potential η ℓ 0) = Real.log N) : Real.log (potential η ℓ T) ≥ -η * bestExpertLoss ℓ := by
  calc Real.log (potential η ℓ T) ≥ Real.log (Real.exp (-η * bestExpertLoss ℓ)) :=
        Real.log_le_log (exp_pos _) (potential_ge_best_expert η hη_pos ℓ)
    _ = -η * bestExpertLoss ℓ := Real.log_exp _

private lemma hedge_regret_bound_aux_hη_ne {N T : Nat} [inst : NeZero N] (η : ℝ) (hη_pos : 0 < η) (hη_le : η ≤ 1) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (hstep : ∀ t : Fin T, Real.log (potential η ℓ (t.val + 1)) - Real.log (potential η ℓ t.val) ≤ -(1 - Real.exp (-η)) * hedgeLoss η ℓ t) (hrelax : ∀ t : Fin T, Real.log (potential η ℓ (t.val + 1)) - Real.log (potential η ℓ t.val) ≤ -η * hedgeLoss η ℓ t + η ^ 2 / 2) (hsum : Real.log (potential η ℓ T) - Real.log (potential η ℓ 0) ≤ -η * hedgeCumLoss η ℓ + η ^ 2 / 2 * T) (hW0 : Real.log (potential η ℓ 0) = Real.log N) (hWT : Real.log (potential η ℓ T) ≥ -η * bestExpertLoss ℓ) : η ≠ 0 :=
  ne_of_gt hη_pos

private lemma hedge_regret_bound_aux_hkey {N T : Nat} [inst : NeZero N] (η : ℝ) (hη_pos : 0 < η) (hη_le : η ≤ 1) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (hstep : ∀ t : Fin T, Real.log (potential η ℓ (t.val + 1)) - Real.log (potential η ℓ t.val) ≤ -(1 - Real.exp (-η)) * hedgeLoss η ℓ t) (hrelax : ∀ t : Fin T, Real.log (potential η ℓ (t.val + 1)) - Real.log (potential η ℓ t.val) ≤ -η * hedgeLoss η ℓ t + η ^ 2 / 2) (hsum : Real.log (potential η ℓ T) - Real.log (potential η ℓ 0) ≤ -η * hedgeCumLoss η ℓ + η ^ 2 / 2 * T) (hW0 : Real.log (potential η ℓ 0) = Real.log N) (hWT : Real.log (potential η ℓ T) ≥ -η * bestExpertLoss ℓ) (hη_ne : η ≠ 0) : η * (hedgeCumLoss η ℓ - bestExpertLoss ℓ) ≤ Real.log ↑N + η ^ 2 / 2 * ↑T := by
  nlinarith

private lemma hedge_regret_bound_aux_hrhs__dup2 {N T : Nat} [inst : NeZero N] (η : ℝ) (hη_pos : 0 < η) (hη_le : η ≤ 1) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (hstep : ∀ t : Fin T, Real.log (potential η ℓ (t.val + 1)) - Real.log (potential η ℓ t.val) ≤ -(1 - Real.exp (-η)) * hedgeLoss η ℓ t) (hrelax : ∀ t : Fin T, Real.log (potential η ℓ (t.val + 1)) - Real.log (potential η ℓ t.val) ≤ -η * hedgeLoss η ℓ t + η ^ 2 / 2) (hsum : Real.log (potential η ℓ T) - Real.log (potential η ℓ 0) ≤ -η * hedgeCumLoss η ℓ + η ^ 2 / 2 * T) (hW0 : Real.log (potential η ℓ 0) = Real.log N) (hWT : Real.log (potential η ℓ T) ≥ -η * bestExpertLoss ℓ) (hη_ne : η ≠ 0) (hkey : η * (hedgeCumLoss η ℓ - bestExpertLoss ℓ) ≤ Real.log ↑N + η ^ 2 / 2 * ↑T) : Real.log ↑N / η + η * ↑T / 2 = (Real.log ↑N + η ^ 2 / 2 * ↑T) / η := by
  field_simp

theorem hedge_regret_bound {N T : ℕ} [NeZero N] (η : ℝ)
    (hη_pos : 0 < η) (hη_le : η ≤ 1)
    (ℓ : LossSeq N T) (hℓ : ℓ.Valid) :
    regret η ℓ ≤ Real.log N / η + η * T / 2 := by
  -- This is the looser regret bound.  It uses the linear exponential estimate
  -- plus `1 - exp(-η) ≥ η - η^2/2`, so we assume `η ≤ 1`.
  -- Step 1: Telescope the log potential steps
  -- Step 2: Each step bound relaxed using one_sub_exp_neg_ge
  let hrelax : ∀ t : Fin T, Real.log (potential η ℓ (t.val + 1)) - Real.log (potential η ℓ t.val) ≤ -η * hedgeLoss η ℓ t + η ^ 2 / 2 := (hedge_regret_bound_aux_hrelax η hη_pos hη_le ℓ hℓ (hedge_regret_bound_aux_hstep η hη_pos hη_le ℓ hℓ))
  -- Step 3: Telescoping sum
  -- We prove: log W_T - log W_0 ≤ -η * hedgeCumLoss + η²T/2
  -- by summing hrelax over all t.
  let hsum : Real.log (potential η ℓ T) - Real.log (potential η ℓ 0) ≤ -η * hedgeCumLoss η ℓ + η ^ 2 / 2 * T := (hedge_regret_bound_aux_hsum η hη_pos hη_le ℓ hℓ (hedge_regret_bound_aux_hstep η hη_pos hη_le ℓ hℓ) hrelax)
  -- Step 4: Use potential_zero and potential_ge_best_expert
  let hW0 : Real.log (potential η ℓ 0) = Real.log N := (hedge_regret_bound_aux_hW0 η hη_pos hη_le ℓ hℓ (hedge_regret_bound_aux_hstep η hη_pos hη_le ℓ hℓ) hrelax hsum)
  -- Step 5: Combine everything
  -- -η * bestExpertLoss - log N ≤ -η * hedgeCumLoss + η²T/2
  -- η * regret ≤ log N + η²T/2
  -- regret ≤ log N / η + ηT/2
  unfold regret
  let hη_ne : η ≠ 0 := (hedge_regret_bound_aux_hη_ne η hη_pos hη_le ℓ hℓ (hedge_regret_bound_aux_hstep η hη_pos hη_le ℓ hℓ) hrelax hsum hW0 (hedge_regret_bound_aux_hWT η hη_pos hη_le ℓ hℓ (hedge_regret_bound_aux_hstep η hη_pos hη_le ℓ hℓ) hrelax hsum hW0))
  let hkey : η * (hedgeCumLoss η ℓ - bestExpertLoss ℓ) ≤ Real.log ↑N + η ^ 2 / 2 * ↑T := (hedge_regret_bound_aux_hkey η hη_pos hη_le ℓ hℓ (hedge_regret_bound_aux_hstep η hη_pos hη_le ℓ hℓ) hrelax hsum hW0 (hedge_regret_bound_aux_hWT η hη_pos hη_le ℓ hℓ (hedge_regret_bound_aux_hstep η hη_pos hη_le ℓ hℓ) hrelax hsum hW0) hη_ne)
  rw [(hedge_regret_bound_aux_hrhs__dup2 η hη_pos hη_le ℓ hℓ (hedge_regret_bound_aux_hstep η hη_pos hη_le ℓ hℓ) hrelax hsum hW0 (hedge_regret_bound_aux_hWT η hη_pos hη_le ℓ hℓ (hedge_regret_bound_aux_hstep η hη_pos hη_le ℓ hℓ) hrelax hsum hW0) hη_ne hkey)]
  rw [mul_comm] at hkey
  exact (le_div_iff₀ hη_pos).mpr hkey

/-! ## No-Regret Corollary -/

/-- Optimal learning rate for T rounds and N experts. -/
-- This learning rate optimizes the looser `ηT/2` bound, subject to the later
-- theorem's assumption that `η ≤ 1`.
noncomputable def optimalEta (N T : ℕ) : ℝ :=
  Real.sqrt (2 * Real.log N / T)

/-- With optimal η = √(2 ln N / T), regret ≤ √(2 T ln N).
    Assumes T ≥ 2 ln N so that η ≤ 1. -/
private lemma hedge_regret_optimal_aux_hN_pos {N T : Nat} [inst : NeZero N] (hT : 0 < T) (hN : 1 < N) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (a : ℝ) (hT_large : 2 * a ≤ ↑T) (ha_def : a = log ↑N) (η : ℝ) (hη_def : η = optimalEta N T) : (1 : ℝ) < ↑N := by
  exact_mod_cast hN

private lemma hedge_regret_optimal_aux_ha_pos {N T : Nat} [inst : NeZero N] (hT : 0 < T) (hN : 1 < N) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (a : ℝ) (hT_large : 2 * a ≤ ↑T) (ha_def : a = log ↑N) (η : ℝ) (hη_def : η = optimalEta N T) (hN_pos : (1 : ℝ) < ↑N) : 0 < log ↑N :=
  Real.log_pos hN_pos

private lemma hedge_regret_optimal_aux_hT_pos {N T : Nat} [inst : NeZero N] (hT : 0 < T) (hN : 1 < N) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (a : ℝ) (hT_large : 2 * a ≤ ↑T) (ha_def : a = log ↑N) (η : ℝ) (hη_def : η = optimalEta N T) (hN_pos : (1 : ℝ) < ↑N) (ha_pos : 0 < log ↑N) : (0 : ℝ) < ↑T :=
  Nat.cast_pos.mpr hT

private lemma hedge_regret_optimal_aux_hT_ne {N T : Nat} [inst : NeZero N] (hT : 0 < T) (hN : 1 < N) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (a : ℝ) (hT_large : 2 * a ≤ ↑T) (ha_def : a = log ↑N) (η : ℝ) (hη_def : η = optimalEta N T) (hN_pos : (1 : ℝ) < ↑N) (ha_pos : 0 < log ↑N) (hT_pos : (0 : ℝ) < ↑T) : (T : ℝ) ≠ 0 :=
  ne_of_gt hT_pos

private lemma hedge_regret_optimal_aux_hη_pos {N T : Nat} [inst : NeZero N] (hT : 0 < T) (hN : 1 < N) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (a : ℝ) (hT_large : 2 * a ≤ ↑T) (ha_def : a = log ↑N) (η : ℝ) (hη_def : η = optimalEta N T) (hN_pos : (1 : ℝ) < ↑N) (ha_pos : 0 < log ↑N) (hT_pos : (0 : ℝ) < ↑T) (hT_ne : (T : ℝ) ≠ 0) (hη_eq : η = Real.sqrt (2 * a / ↑T)) : 0 < η := by
  rw [hη_eq]; exact Real.sqrt_pos.mpr (div_pos (by linarith) hT_pos)

private lemma hedge_regret_optimal_aux_hη_sq {N T : Nat} [inst : NeZero N] (hT : 0 < T) (hN : 1 < N) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (a : ℝ) (hT_large : 2 * a ≤ ↑T) (ha_def : a = log ↑N) (η : ℝ) (hη_def : η = optimalEta N T) (hN_pos : (1 : ℝ) < ↑N) (ha_pos : 0 < log ↑N) (hT_pos : (0 : ℝ) < ↑T) (hT_ne : (T : ℝ) ≠ 0) (hη_eq : η = Real.sqrt (2 * a / ↑T)) (hη_pos : 0 < η) : η ^ 2 = 2 * a / ↑T := by
  rw [hη_eq, sq_sqrt (le_of_lt (div_pos (by linarith) hT_pos))]

private lemma hedge_regret_optimal_aux_hη_le {N T : Nat} [inst : NeZero N] (hT : 0 < T) (hN : 1 < N) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (a : ℝ) (hT_large : 2 * a ≤ ↑T) (ha_def : a = log ↑N) (η : ℝ) (hη_def : η = optimalEta N T) (hN_pos : (1 : ℝ) < ↑N) (ha_pos : 0 < log ↑N) (hT_pos : (0 : ℝ) < ↑T) (hT_ne : (T : ℝ) ≠ 0) (hη_eq : η = Real.sqrt (2 * a / ↑T)) (hη_pos : 0 < η) (hη_sq : η ^ 2 = 2 * a / ↑T) : optimalEta N T ≤ 1 := by
  rw [← Real.sqrt_one]
  exact Real.sqrt_le_sqrt (by rw [div_le_one hT_pos]; linarith [ha_def])

private lemma hedge_regret_optimal_aux_hrhs_nn {N T : Nat} [inst : NeZero N] (hT : 0 < T) (hN : 1 < N) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (a : ℝ) (hT_large : 2 * a ≤ ↑T) (ha_def : a = log ↑N) (η : ℝ) (hη_def : η = optimalEta N T) (hN_pos : (1 : ℝ) < ↑N) (ha_pos : 0 < log ↑N) (hT_pos : (0 : ℝ) < ↑T) (hT_ne : (T : ℝ) ≠ 0) (hη_eq : η = Real.sqrt (2 * a / ↑T)) (hη_pos : 0 < η) (hη_sq : η ^ 2 = 2 * a / ↑T) (hη_le : optimalEta N T ≤ 1) (hbound : regret η ℓ ≤ log ↑N / η + η * ↑T / 2) (hlhs_nn : 0 ≤ a / η + η * ↑T / 2) : 0 ≤ Real.sqrt (2 * ↑T * a) :=
  Real.sqrt_nonneg _

private lemma hedge_regret_optimal_aux_hη_ne {N T : Nat} [inst : NeZero N] (hT : 0 < T) (hN : 1 < N) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (a : ℝ) (hT_large : 2 * a ≤ ↑T) (ha_def : a = log ↑N) (η : ℝ) (hη_def : η = optimalEta N T) (hN_pos : (1 : ℝ) < ↑N) (ha_pos : 0 < log ↑N) (hT_pos : (0 : ℝ) < ↑T) (hT_ne : (T : ℝ) ≠ 0) (hη_eq : η = Real.sqrt (2 * a / ↑T)) (hη_pos : 0 < η) (hη_sq : η ^ 2 = 2 * a / ↑T) (hη_le : optimalEta N T ≤ 1) (hbound : regret η ℓ ≤ log ↑N / η + η * ↑T / 2) (hlhs_nn : 0 ≤ a / η + η * ↑T / 2) (hrhs_nn : 0 ≤ Real.sqrt (2 * ↑T * a)) : η ≠ 0 :=
  ne_of_gt hη_pos

private lemma hedge_regret_optimal_aux_hηT {N T : Nat} [inst : NeZero N] (hT : 0 < T) (hN : 1 < N) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (a : ℝ) (hT_large : 2 * a ≤ ↑T) (ha_def : a = log ↑N) (η : ℝ) (hη_def : η = optimalEta N T) (hN_pos : (1 : ℝ) < ↑N) (ha_pos : 0 < log ↑N) (hT_pos : (0 : ℝ) < ↑T) (hT_ne : (T : ℝ) ≠ 0) (hη_eq : η = Real.sqrt (2 * a / ↑T)) (hη_pos : 0 < η) (hη_sq : η ^ 2 = 2 * a / ↑T) (hη_le : optimalEta N T ≤ 1) (hbound : regret η ℓ ≤ log ↑N / η + η * ↑T / 2) (hlhs_nn : 0 ≤ a / η + η * ↑T / 2) (hrhs_nn : 0 ≤ Real.sqrt (2 * ↑T * a)) (hη_ne : η ≠ 0) : η ^ 2 * ↑T = 2 * a := by
  rw [hη_sq]; field_simp

private lemma hedge_regret_optimal_aux_hprod {N T : Nat} [inst : NeZero N] (hT : 0 < T) (hN : 1 < N) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (a : ℝ) (hT_large : 2 * a ≤ ↑T) (ha_def : a = log ↑N) (η : ℝ) (hη_def : η = optimalEta N T) (hN_pos : (1 : ℝ) < ↑N) (ha_pos : 0 < log ↑N) (hT_pos : (0 : ℝ) < ↑T) (hT_ne : (T : ℝ) ≠ 0) (hη_eq : η = Real.sqrt (2 * a / ↑T)) (hη_pos : 0 < η) (hη_sq : η ^ 2 = 2 * a / ↑T) (hη_le : optimalEta N T ≤ 1) (hbound : regret η ℓ ≤ log ↑N / η + η * ↑T / 2) (hlhs_nn : 0 ≤ a / η + η * ↑T / 2) (hrhs_nn : 0 ≤ Real.sqrt (2 * ↑T * a)) (hη_ne : η ≠ 0) (hηT : η ^ 2 * ↑T = 2 * a) : (a / η + η * ↑T / 2) * η = 2 * a := by
  rw [add_mul, div_mul_cancel₀ a hη_ne]
  linarith [hηT]

private lemma hedge_regret_optimal_aux_h1 {N T : Nat} [inst : NeZero N] (hT : 0 < T) (hN : 1 < N) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (a : ℝ) (hT_large : 2 * a ≤ ↑T) (ha_def : a = log ↑N) (η : ℝ) (hη_def : η = optimalEta N T) (hN_pos : (1 : ℝ) < ↑N) (ha_pos : 0 < log ↑N) (hT_pos : (0 : ℝ) < ↑T) (hT_ne : (T : ℝ) ≠ 0) (hη_eq : η = Real.sqrt (2 * a / ↑T)) (hη_pos : 0 < η) (hη_sq : η ^ 2 = 2 * a / ↑T) (hη_le : optimalEta N T ≤ 1) (hbound : regret η ℓ ≤ log ↑N / η + η * ↑T / 2) (hlhs_nn : 0 ≤ a / η + η * ↑T / 2) (hrhs_nn : 0 ≤ Real.sqrt (2 * ↑T * a)) (hη_ne : η ≠ 0) (hηT : η ^ 2 * ↑T = 2 * a) (hprod : (a / η + η * ↑T / 2) * η = 2 * a) : a / η + η * ↑T / 2 = 2 * a / η := by
  rw [eq_div_iff hη_ne]; linarith [hprod]

private lemma hedge_regret_optimal_aux_h_anon_1 {N T : Nat} [inst : NeZero N] (hT : 0 < T) (hN : 1 < N) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (a : ℝ) (hT_large : 2 * a ≤ ↑T) (ha_def : a = log ↑N) (η : ℝ) (hη_def : η = optimalEta N T) (hN_pos : (1 : ℝ) < ↑N) (ha_pos : 0 < log ↑N) (hT_pos : (0 : ℝ) < ↑T) (hT_ne : (T : ℝ) ≠ 0) (hη_eq : η = Real.sqrt (2 * a / ↑T)) (hη_pos : 0 < η) (hη_sq : η ^ 2 = 2 * a / ↑T) (hη_le : optimalEta N T ≤ 1) (hbound : regret η ℓ ≤ log ↑N / η + η * ↑T / 2) (hlhs_nn : 0 ≤ a / η + η * ↑T / 2) (hrhs_nn : 0 ≤ Real.sqrt (2 * ↑T * a)) (hη_ne : η ≠ 0) (hηT : η ^ 2 * ↑T = 2 * a) (hprod : (a / η + η * ↑T / 2) * η = 2 * a) (h1 : a / η + η * ↑T / 2 = 2 * a / η) : η ^ 2 = 2 * a / ↑T :=
  hη_sq

private lemma hedge_regret_optimal_aux_hsq {N T : Nat} [inst : NeZero N] (hT : 0 < T) (hN : 1 < N) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (a : ℝ) (hT_large : 2 * a ≤ ↑T) (ha_def : a = log ↑N) (η : ℝ) (hη_def : η = optimalEta N T) (hN_pos : (1 : ℝ) < ↑N) (ha_pos : 0 < log ↑N) (hT_pos : (0 : ℝ) < ↑T) (hT_ne : (T : ℝ) ≠ 0) (hη_eq : η = Real.sqrt (2 * a / ↑T)) (hη_pos : 0 < η) (hη_sq : η ^ 2 = 2 * a / ↑T) (hη_le : optimalEta N T ≤ 1) (hbound : regret η ℓ ≤ log ↑N / η + η * ↑T / 2) (hlhs_nn : 0 ≤ a / η + η * ↑T / 2) (hrhs_nn : 0 ≤ Real.sqrt (2 * ↑T * a)) (hη_ne : η ≠ 0) (hηT : η ^ 2 * ↑T = 2 * a) (hprod : (a / η + η * ↑T / 2) * η = 2 * a) : (a / η + η * ↑T / 2) ^ 2 = 2 * ↑T * a := by
  rw [(hedge_regret_optimal_aux_h1 hT hN ℓ hℓ a hT_large ha_def η hη_def hN_pos ha_pos hT_pos hT_ne hη_eq hη_pos hη_sq hη_le hbound hlhs_nn hrhs_nn hη_ne hηT hprod), div_pow]
  let h_anon_1 : η ^ 2 = 2 * a / ↑T := (hedge_regret_optimal_aux_h_anon_1 hT hN ℓ hℓ a hT_large ha_def η hη_def hN_pos ha_pos hT_pos hT_ne hη_eq hη_pos hη_sq hη_le hbound hlhs_nn hrhs_nn hη_ne hηT hprod (hedge_regret_optimal_aux_h1 hT hN ℓ hℓ a hT_large ha_def η hη_def hN_pos ha_pos hT_pos hT_ne hη_eq hη_pos hη_sq hη_le hbound hlhs_nn hrhs_nn hη_ne hηT hprod))
  field_simp [hη_ne]
  nlinarith [hη_sq, sq_nonneg a]

theorem hedge_regret_optimal {N T : ℕ} [NeZero N]
    (hT : 0 < T) (hN : 1 < N)
    (hT_large : 2 * Real.log N ≤ T)
    (ℓ : LossSeq N T) (hℓ : ℓ.Valid) :
    regret (optimalEta N T) ℓ ≤ Real.sqrt (2 * T * Real.log N) := by
  -- This theorem is mostly algebra: plug the chosen `η` into the previous
  -- bound, then show the two terms balance.
  set a := Real.log ↑N with ha_def
  set η := optimalEta N T with hη_def
  let hN_pos : (1 : ℝ) < ↑N := (hedge_regret_optimal_aux_hN_pos hT hN ℓ hℓ a hT_large ha_def η hη_def)
  let ha_pos : 0 < log ↑N := (hedge_regret_optimal_aux_ha_pos hT hN ℓ hℓ a hT_large ha_def η hη_def hN_pos)
  let hT_pos : (0 : ℝ) < ↑T := (hedge_regret_optimal_aux_hT_pos hT hN ℓ hℓ a hT_large ha_def η hη_def hN_pos ha_pos)
  let hT_ne : (T : ℝ) ≠ 0 := (hedge_regret_optimal_aux_hT_ne hT hN ℓ hℓ a hT_large ha_def η hη_def hN_pos ha_pos hT_pos)
  -- η = √(2a/T)

  -- η > 0
  let hη_pos : 0 < η := (hedge_regret_optimal_aux_hη_pos hT hN ℓ hℓ a hT_large ha_def η hη_def hN_pos ha_pos hT_pos hT_ne (rfl))
  -- η² = 2a/T
  let hη_sq : η ^ 2 = 2 * a / ↑T := (hedge_regret_optimal_aux_hη_sq hT hN ℓ hℓ a hT_large ha_def η hη_def hN_pos ha_pos hT_pos hT_ne (rfl) hη_pos)
  -- η ≤ 1 (from hT_large: T ≥ 2a, so η² = 2a/T ≤ 1)
  let hη_le : optimalEta N T ≤ 1 := (hedge_regret_optimal_aux_hη_le hT hN ℓ hℓ a hT_large ha_def η hη_def hN_pos ha_pos hT_pos hT_ne (rfl) hη_pos hη_sq)
  -- Apply main bound
  let hbound := hedge_regret_bound η hη_pos hη_le ℓ hℓ
  -- Show: a/η + ηT/2 = √(2aT)
  -- Key: (a/η + ηT/2)² = a²/η² + aT + η²T²/4
  --       = a²T/(2a) + aT + (2a/T)*T²/4 = aT/2 + aT + aT/2 = 2aT
  suffices hsuff : a / η + η * ↑T / 2 = Real.sqrt (2 * ↑T * a) by
    linarith [hN_pos]
  -- Both sides are nonneg, so we can square
  let hlhs_nn : 0 ≤ a / η + η * ↑T / 2 := by positivity
  let hrhs_nn : 0 ≤ Real.sqrt (2 * ↑T * a) := (hedge_regret_optimal_aux_hrhs_nn hT hN ℓ hℓ a hT_large ha_def η hη_def hN_pos ha_pos hT_pos hT_ne (rfl) hη_pos hη_sq hη_le hbound hlhs_nn)
  rw [← Real.sqrt_sq hlhs_nn]
  congr 1
  let hη_ne : η ≠ 0 := (hedge_regret_optimal_aux_hη_ne hT hN ℓ hℓ a hT_large ha_def η hη_def hN_pos ha_pos hT_pos hT_ne (rfl) hη_pos hη_sq hη_le hbound hlhs_nn hrhs_nn)
  -- Compute (a/η + ηT/2)² = 2aT using η² = 2a/T

  -- a/η = a*η/η² = a*η/(2a/T) = ... but let's work with η² directly
  -- (a/η + ηT/2)² = a²/η² + aT + η²T²/4
  -- Multiply through by η²: η²(a/η + ηT/2)² = a² + aT*η² + η⁴T²/4
  -- = a² + a*2a + (2a/T)²*T²/4 = a² + 2a² + a² = 4a²... no that's wrong.
  -- Let's compute (a/η + ηT/2) * η = a + η²T/2 = a + a = 2a

  -- So a/η + ηT/2 = 2a/η
  -- (2a/η)² = 4a²/η² = 4a²*T/(2a) = 2aT ✓
  let hsq : (a / η + η * ↑T / 2) ^ 2 = 2 * ↑T * a := (hedge_regret_optimal_aux_hsq hT hN ℓ hℓ a hT_large ha_def η hη_def hN_pos ha_pos hT_pos hT_ne (rfl) hη_pos hη_sq hη_le hbound hlhs_nn hrhs_nn hη_ne ((hedge_regret_optimal_aux_hηT hT hN ℓ hℓ a hT_large ha_def η hη_def hN_pos ha_pos hT_pos hT_ne (rfl) hη_pos hη_sq hη_le hbound hlhs_nn hrhs_nn hη_ne)) ((hedge_regret_optimal_aux_hprod hT hN ℓ hℓ a hT_large ha_def η hη_def hN_pos ha_pos hT_pos hT_ne (rfl) hη_pos hη_sq hη_le hbound hlhs_nn hrhs_nn hη_ne ((hedge_regret_optimal_aux_hηT hT hN ℓ hℓ a hT_large ha_def η hη_def hN_pos ha_pos hT_pos hT_ne (rfl) hη_pos hη_sq hη_le hbound hlhs_nn hrhs_nn hη_ne)))))
  rw [← Real.sqrt_sq hlhs_nn, hsq, Real.sq_sqrt (by positivity)]

/-- **Hedge is no-regret**: average regret ≤ √(2 ln N / T) → 0 as T → ∞. -/
private lemma hedge_no_regret_aux_hT_pos {N T : Nat} [inst : NeZero N] (hT : 0 < T) (hN : 1 < N) (hT_large : 2 * log ↑N ≤ ↑T) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) : (0 : ℝ) < ↑T :=
  Nat.cast_pos.mpr hT

private lemma hedge_no_regret_aux_hN_pos {N T : Nat} [inst : NeZero N] (hT : 0 < T) (hN : 1 < N) (hT_large : 2 * log ↑N ≤ ↑T) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (hT_pos : (0 : ℝ) < ↑T) : (1 : ℝ) < ↑N := by
  exact_mod_cast hN

private lemma hedge_no_regret_aux_hlogN {N T : Nat} [inst : NeZero N] (hT : 0 < T) (hN : 1 < N) (hT_large : 2 * log ↑N ≤ ↑T) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (hT_pos : (0 : ℝ) < ↑T) (hN_pos : (1 : ℝ) < ↑N) : 0 < Real.log ↑N :=
  Real.log_pos hN_pos

private lemma hedge_no_regret_aux_hopt {N T : Nat} [inst : NeZero N] (hT : 0 < T) (hN : 1 < N) (hT_large : 2 * log ↑N ≤ ↑T) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (hT_pos : (0 : ℝ) < ↑T) (hN_pos : (1 : ℝ) < ↑N) (hlogN : 0 < Real.log ↑N) : regret (optimalEta N T) ℓ ≤ √(2 * ↑T * log ↑N) :=
  hedge_regret_optimal hT hN hT_large ℓ hℓ

private lemma hedge_no_regret_aux_h1 {N T : Nat} [inst : NeZero N] (hT : 0 < T) (hN : 1 < N) (hT_large : 2 * log ↑N ≤ ↑T) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (hT_pos : (0 : ℝ) < ↑T) (hN_pos : (1 : ℝ) < ↑N) (hlogN : 0 < Real.log ↑N) (hopt : regret (optimalEta N T) ℓ ≤ √(2 * ↑T * log ↑N)) : regret (optimalEta N T) ℓ / ↑T ≤ Real.sqrt (2 * ↑T * Real.log N) / ↑T :=
  div_le_div_of_nonneg_right hopt hT_pos.le

private lemma hedge_no_regret_aux_hlhs_nn {N T : Nat} [inst : NeZero N] (hT : 0 < T) (hN : 1 < N) (hT_large : 2 * log ↑N ≤ ↑T) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (hT_pos : (0 : ℝ) < ↑T) (hN_pos : (1 : ℝ) < ↑N) (hlogN : 0 < Real.log ↑N) (hopt : regret (optimalEta N T) ℓ ≤ √(2 * ↑T * log ↑N)) (h1 : regret (optimalEta N T) ℓ / ↑T ≤ Real.sqrt (2 * ↑T * Real.log N) / ↑T) : 0 ≤ Real.sqrt (2 * ↑T * Real.log N) / ↑T :=
  div_nonneg (Real.sqrt_nonneg _) hT_pos.le

theorem hedge_no_regret {N T : ℕ} [NeZero N]
    (hT : 0 < T) (hN : 1 < N)
    (hT_large : 2 * Real.log N ≤ T)
    (ℓ : LossSeq N T) (hℓ : ℓ.Valid) :
    regret (optimalEta N T) ℓ / T ≤ Real.sqrt (2 * Real.log N / T) := by
  -- Divide the optimized cumulative regret bound by `T`.  The right side goes
  -- to zero as `T` grows with `N` fixed, which is the no-regret statement.

  let hN_pos : (1 : ℝ) < ↑N := (hedge_no_regret_aux_hN_pos hT hN hT_large ℓ hℓ ((hedge_no_regret_aux_hT_pos hT hN hT_large ℓ hℓ)))

  let hopt : regret (optimalEta N T) ℓ ≤ √(2 * ↑T * log ↑N) := (hedge_no_regret_aux_hopt hT hN hT_large ℓ hℓ ((hedge_no_regret_aux_hT_pos hT hN hT_large ℓ hℓ)) hN_pos ((hedge_no_regret_aux_hlogN hT hN hT_large ℓ hℓ ((hedge_no_regret_aux_hT_pos hT hN hT_large ℓ hℓ)) hN_pos)))
  -- regret / T ≤ √(2T ln N) / T
  let h1 : regret (optimalEta N T) ℓ / ↑T ≤ Real.sqrt (2 * ↑T * Real.log N) / ↑T := (hedge_no_regret_aux_h1 hT hN hT_large ℓ hℓ ((hedge_no_regret_aux_hT_pos hT hN hT_large ℓ hℓ)) hN_pos ((hedge_no_regret_aux_hlogN hT hN hT_large ℓ hℓ ((hedge_no_regret_aux_hT_pos hT hN hT_large ℓ hℓ)) hN_pos)) hopt)
  -- √(2T ln N) / T = √(2 ln N / T)
  -- Proof: both sides are nonneg, and squaring gives 2T ln N / T² = 2 ln N / T ✓
  suffices hsuff : Real.sqrt (2 * ↑T * Real.log N) / ↑T = Real.sqrt (2 * Real.log N / ↑T) by
    linarith [hN_pos]

  rw [← Real.sqrt_sq ((hedge_no_regret_aux_hlhs_nn hT hN hT_large ℓ hℓ ((hedge_no_regret_aux_hT_pos hT hN hT_large ℓ hℓ)) hN_pos ((hedge_no_regret_aux_hlogN hT hN hT_large ℓ hℓ ((hedge_no_regret_aux_hT_pos hT hN hT_large ℓ hℓ)) hN_pos)) hopt h1)), ← Real.sqrt_sq (Real.sqrt_nonneg _)]
  congr 1
  rw [div_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  field_simp

/-! ## Tight Bound via Hoeffding's Lemma -/

/-!
The previous proof loses a factor in the step where `1 - exp(-η)` is relaxed.
The tight section replaces that relaxation with Hoeffding's lemma.  This gives
the sharper per-round term `η^2 / 8`, hence final regret
`(log N) / η + ηT / 8`.
-/

/-- **Hoeffding's lemma**: for p ∈ [0,1] and any h ∈ ℝ,
    ln((1-p) + p·eʰ) ≤ p·h + h²/8.

    Specializes `bernoulli_mgf_bound` (the Bernoulli case of Hoeffding's inequality
    from `Hedge.Hoeffding`) by substituting η = -h. -/
private lemma hoeffding_lemma_aux_hb {p h : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : log (1 - p + p * rexp (- -h)) ≤ -p * -h + (-h) ^ 2 / 8 :=
  bernoulli_mgf_bound p (-h) hp0 hp1

lemma hoeffding_lemma {p h : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Real.log ((1 - p) + p * Real.exp h) ≤ p * h + h ^ 2 / 8 := by
  let hb : log (1 - p + p * rexp (- -h)) ≤ -p * -h + (-h) ^ 2 / 8 := (hoeffding_lemma_aux_hb hp0 hp1)
  simp only [neg_neg] at hb
  linarith [show -p * -h + (-h) ^ 2 / 8 = p * h + h ^ 2 / 8 from by ring]

/-- Tight per-step bound using Hoeffding's lemma:
    ln W_{t+1} - ln W_t ≤ -η · hedgeLoss_t + η²/8. -/
private lemma log_potential_step_tight_aux_hWt {N T : Nat} [inst : NeZero N] (η : ℝ) (hη : 0 < η) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (t : Fin T) (ht : ↑t + 1 ≤ T) : 0 < potential η ℓ ↑t :=
  potential_pos η ℓ t.val

private lemma log_potential_step_tight_aux_hWt1 {N T : Nat} [inst : NeZero N] (η : ℝ) (hη : 0 < η) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (t : Fin T) (ht : ↑t + 1 ≤ T) (hWt : 0 < potential η ℓ ↑t) : 0 < potential η ℓ (↑t + 1) :=
  potential_pos η ℓ (t.val + 1)

private lemma log_potential_step_tight_aux_hratio {N T : Nat} [inst : NeZero N] (η : ℝ) (hη : 0 < η) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (t : Fin T) (ht : ↑t + 1 ≤ T) (hWt : 0 < potential η ℓ ↑t) (hWt1 : 0 < potential η ℓ (↑t + 1)) : potential η ℓ (↑t + 1) / potential η ℓ ↑t ≤ 1 - (1 - rexp (-η)) * hedgeLoss η ℓ t :=
  potential_ratio_le η hη ℓ hℓ t ht

private lemma log_potential_step_tight_aux_hμ0 {N T : Nat} [inst : NeZero N] (η : ℝ) (hη : 0 < η) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (t : Fin T) (ht : ↑t + 1 ≤ T) (hWt : 0 < potential η ℓ ↑t) (hWt1 : 0 < potential η ℓ (↑t + 1)) (μ : ℝ) (hratio : potential η ℓ (↑t + 1) / potential η ℓ ↑t ≤ 1 - (1 - rexp (-η)) * hedgeLoss η ℓ t) : 0 ≤ hedgeLoss η ℓ t :=
  hedgeLoss_nonneg η ℓ hℓ t

private lemma log_potential_step_tight_aux_hμ1 {N T : Nat} [inst : NeZero N] (η : ℝ) (hη : 0 < η) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (t : Fin T) (ht : ↑t + 1 ≤ T) (hWt : 0 < potential η ℓ ↑t) (hWt1 : 0 < potential η ℓ (↑t + 1)) (μ : ℝ) (hratio : potential η ℓ (↑t + 1) / potential η ℓ ↑t ≤ 1 - (1 - rexp (-η)) * hedgeLoss η ℓ t) (hμ0 : 0 ≤ hedgeLoss η ℓ t) : hedgeLoss η ℓ t ≤ 1 :=
  hedgeLoss_le_one η ℓ hℓ t

private lemma log_potential_step_tight_aux_hratio_pos {N T : Nat} [inst : NeZero N] (η : ℝ) (hη : 0 < η) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (t : Fin T) (ht : ↑t + 1 ≤ T) (hWt : 0 < potential η ℓ ↑t) (hWt1 : 0 < potential η ℓ (↑t + 1)) (μ : ℝ) (hratio : potential η ℓ (↑t + 1) / potential η ℓ ↑t ≤ 1 - (1 - rexp (-η)) * hedgeLoss η ℓ t) (hμ0 : 0 ≤ hedgeLoss η ℓ t) (hμ1 : hedgeLoss η ℓ t ≤ 1) : 0 < potential η ℓ (t.val + 1) / potential η ℓ t.val :=
  div_pos hWt1 hWt

private lemma log_potential_step_tight_aux_hcomp {N T : Nat} [inst : NeZero N] (η : ℝ) (hη : 0 < η) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (t : Fin T) (ht : ↑t + 1 ≤ T) (hWt : 0 < potential η ℓ ↑t) (hWt1 : 0 < potential η ℓ (↑t + 1)) (μ : ℝ) (hratio : potential η ℓ (↑t + 1) / potential η ℓ ↑t ≤ 1 - (1 - rexp (-η)) * hedgeLoss η ℓ t) (hμ0 : 0 ≤ hedgeLoss η ℓ t) (hμ1 : hedgeLoss η ℓ t ≤ 1) (hratio_pos : 0 < potential η ℓ (t.val + 1) / potential η ℓ t.val) : 1 - (1 - Real.exp (-η)) * μ = (1 - μ) + μ * Real.exp (-η) := by
  ring

lemma log_potential_step_tight {N T : ℕ} [NeZero N] (η : ℝ) (hη : 0 < η)
    (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (t : Fin T) (ht : t.val + 1 ≤ T) :
    Real.log (potential η ℓ (t.val + 1)) - Real.log (potential η ℓ t.val)
      ≤ -η * hedgeLoss η ℓ t + η ^ 2 / 8 := by
  -- Here `μ = hedgeLoss` lies in `[0,1]`.  The one-step potential ratio is
  -- bounded by `(1-μ) + μ exp(-η)`, and Hoeffding converts the logarithm of
  -- that expression into `-η μ + η^2/8`.
  let hWt : 0 < potential η ℓ ↑t := (log_potential_step_tight_aux_hWt η hη ℓ hℓ t ht)
  rw [← Real.log_div (ne_of_gt (log_potential_step_tight_aux_hWt1 η hη ℓ hℓ t ht hWt)) (ne_of_gt hWt)]
  let hratio : potential η ℓ (↑t + 1) / potential η ℓ ↑t ≤ 1 - (1 - rexp (-η)) * hedgeLoss η ℓ t := (log_potential_step_tight_aux_hratio η hη ℓ hℓ t ht hWt (log_potential_step_tight_aux_hWt1 η hη ℓ hℓ t ht hWt))
  -- W_{t+1}/W_t ≤ (1-μ) + μ·e^{-η} where μ = hedgeLoss
  -- Apply Hoeffding with p = μ, h = -η
  set μ := hedgeLoss η ℓ t
  let hμ0 : 0 ≤ hedgeLoss η ℓ t := (log_potential_step_tight_aux_hμ0 η hη ℓ hℓ t ht hWt (log_potential_step_tight_aux_hWt1 η hη ℓ hℓ t ht hWt) μ hratio)
  let hratio_pos : 0 < potential η ℓ (t.val + 1) / potential η ℓ t.val := (log_potential_step_tight_aux_hratio_pos η hη ℓ hℓ t ht hWt (log_potential_step_tight_aux_hWt1 η hη ℓ hℓ t ht hWt) μ hratio hμ0 (log_potential_step_tight_aux_hμ1 η hη ℓ hℓ t ht hWt (log_potential_step_tight_aux_hWt1 η hη ℓ hℓ t ht hWt) μ hratio hμ0))
  -- The ratio is ≤ (1-μ) + μ·e^{-η}
  -- Apply log monotonicity then Hoeffding
  calc Real.log (potential η ℓ (t.val + 1) / potential η ℓ t.val)
      ≤ Real.log ((1 - μ) + μ * Real.exp (-η)) := by
        apply Real.log_le_log hratio_pos
        linarith [(log_potential_step_tight_aux_hcomp η hη ℓ hℓ t ht hWt (log_potential_step_tight_aux_hWt1 η hη ℓ hℓ t ht hWt) μ hratio hμ0 (log_potential_step_tight_aux_hμ1 η hη ℓ hℓ t ht hWt (log_potential_step_tight_aux_hWt1 η hη ℓ hℓ t ht hWt) μ hratio hμ0) hratio_pos)]
    _ ≤ μ * (-η) + (-η) ^ 2 / 8 :=
        hoeffding_lemma hμ0 (log_potential_step_tight_aux_hμ1 η hη ℓ hℓ t ht hWt (log_potential_step_tight_aux_hWt1 η hη ℓ hℓ t ht hWt) μ hratio hμ0)
    _ = -η * μ + η ^ 2 / 8 := by ring

/-- **Tight Hedge Regret Bound** (Cesa-Bianchi & Lugosi):
    For any valid loss sequence with N experts, T rounds, and η > 0,
    the regret of Hedge is at most (ln N)/η + ηT/8.

    This is the theorem reused by the adaptive-episode layer: once an online
    interaction has generated a valid `LossSeq`, the bound applies directly. -/
private lemma hedge_regret_bound_tight_aux_hstep {N T : Nat} [inst : NeZero N] (η : ℝ) (hη_pos : 0 < η) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (t : Fin T) : Real.log (potential η ℓ (t.val + 1)) - Real.log (potential η ℓ t.val) ≤ -η * hedgeLoss η ℓ t + η ^ 2 / 8 :=
  log_potential_step_tight η hη_pos ℓ hℓ t (by omega)

private lemma hedge_regret_bound_tight_aux_hbounds {N T : Nat} [inst : NeZero N] (η : ℝ) (hη_pos : 0 < η) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (hstep : ∀ t : Fin T, Real.log (potential η ℓ (t.val + 1)) - Real.log (potential η ℓ t.val) ≤ -η * hedgeLoss η ℓ t + η ^ 2 / 8) : ∑ i : Fin T, (log (potential η ℓ (↑i + 1)) - log (potential η ℓ ↑i)) ≤ ∑ i : Fin T, (-η * hedgeLoss η ℓ i + η ^ 2 / 8) :=
  Finset.sum_le_sum fun t (_ : t ∈ Finset.univ) => hstep t

private lemma hedge_regret_bound_tight_aux_hrhs {N T : Nat} [inst : NeZero N] (η : ℝ) (hη_pos : 0 < η) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (hstep : ∀ t : Fin T, Real.log (potential η ℓ (t.val + 1)) - Real.log (potential η ℓ t.val) ≤ -η * hedgeLoss η ℓ t + η ^ 2 / 8) (hbounds : ∑ i : Fin T, (log (potential η ℓ (↑i + 1)) - log (potential η ℓ ↑i)) ≤ ∑ i : Fin T, (-η * hedgeLoss η ℓ i + η ^ 2 / 8)) : ∑ t : Fin T, (-η * hedgeLoss η ℓ t + η ^ 2 / 8) = -η * hedgeCumLoss η ℓ + η ^ 2 / 8 * T := by
  simp only [hedgeCumLoss, Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_fin]
  ring

private lemma hedge_regret_bound_tight_aux_hsum {N T : Nat} [inst : NeZero N] (η : ℝ) (hη_pos : 0 < η) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (hstep : ∀ t : Fin T, Real.log (potential η ℓ (t.val + 1)) - Real.log (potential η ℓ t.val) ≤ -η * hedgeLoss η ℓ t + η ^ 2 / 8) : Real.log (potential η ℓ T) - Real.log (potential η ℓ 0) ≤ -η * hedgeCumLoss η ℓ + η ^ 2 / 8 * T := by

  let hrhs : ∑ t : Fin T, (-η * hedgeLoss η ℓ t + η ^ 2 / 8) = -η * hedgeCumLoss η ℓ + η ^ 2 / 8 * T := (hedge_regret_bound_tight_aux_hrhs η hη_pos ℓ hℓ hstep ((hedge_regret_bound_tight_aux_hbounds η hη_pos ℓ hℓ hstep)))
  suffices htel : ∑ t : Fin T,
      (Real.log (potential η ℓ (t.val + 1)) - Real.log (potential η ℓ t.val)) =
      Real.log (potential η ℓ T) - Real.log (potential η ℓ 0) by linarith [((hedge_regret_bound_tight_aux_hbounds η hη_pos ℓ hℓ hstep))]
  set f := fun n => Real.log (potential η ℓ n)
  show ∑ t : Fin T, (f (t.val + 1) - f t.val) = f T - f 0
  conv_lhs => arg 2; ext t; rw [show t.val = (t : ℕ) from rfl]
  rw [Fin.sum_univ_eq_sum_range (fun n => f (n + 1) - f n)]
  exact Finset.sum_range_sub f T

private lemma hedge_regret_bound_tight_aux_hW0 {N T : Nat} [inst : NeZero N] (η : ℝ) (hη_pos : 0 < η) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (hstep : ∀ t : Fin T, Real.log (potential η ℓ (t.val + 1)) - Real.log (potential η ℓ t.val) ≤ -η * hedgeLoss η ℓ t + η ^ 2 / 8) (hsum : Real.log (potential η ℓ T) - Real.log (potential η ℓ 0) ≤ -η * hedgeCumLoss η ℓ + η ^ 2 / 8 * T) : Real.log (potential η ℓ 0) = Real.log N := by
  rw [potential_zero]

private lemma hedge_regret_bound_tight_aux_hWT {N T : Nat} [inst : NeZero N] (η : ℝ) (hη_pos : 0 < η) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (hstep : ∀ t : Fin T, Real.log (potential η ℓ (t.val + 1)) - Real.log (potential η ℓ t.val) ≤ -η * hedgeLoss η ℓ t + η ^ 2 / 8) (hsum : Real.log (potential η ℓ T) - Real.log (potential η ℓ 0) ≤ -η * hedgeCumLoss η ℓ + η ^ 2 / 8 * T) (hW0 : Real.log (potential η ℓ 0) = Real.log N) : Real.log (potential η ℓ T) ≥ -η * bestExpertLoss ℓ := by
  calc Real.log (potential η ℓ T) ≥ Real.log (Real.exp (-η * bestExpertLoss ℓ)) :=
        Real.log_le_log (exp_pos _) (potential_ge_best_expert η hη_pos ℓ)
    _ = -η * bestExpertLoss ℓ := Real.log_exp _

private lemma hedge_regret_bound_tight_aux_hη_ne {N T : Nat} [inst : NeZero N] (η : ℝ) (hη_pos : 0 < η) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (hstep : ∀ t : Fin T, Real.log (potential η ℓ (t.val + 1)) - Real.log (potential η ℓ t.val) ≤ -η * hedgeLoss η ℓ t + η ^ 2 / 8) (hsum : Real.log (potential η ℓ T) - Real.log (potential η ℓ 0) ≤ -η * hedgeCumLoss η ℓ + η ^ 2 / 8 * T) (hW0 : Real.log (potential η ℓ 0) = Real.log N) (hWT : Real.log (potential η ℓ T) ≥ -η * bestExpertLoss ℓ) : η ≠ 0 :=
  ne_of_gt hη_pos

private lemma hedge_regret_bound_tight_aux_hkey {N T : Nat} [inst : NeZero N] (η : ℝ) (hη_pos : 0 < η) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (hstep : ∀ t : Fin T, Real.log (potential η ℓ (t.val + 1)) - Real.log (potential η ℓ t.val) ≤ -η * hedgeLoss η ℓ t + η ^ 2 / 8) (hsum : Real.log (potential η ℓ T) - Real.log (potential η ℓ 0) ≤ -η * hedgeCumLoss η ℓ + η ^ 2 / 8 * T) (hW0 : Real.log (potential η ℓ 0) = Real.log N) (hWT : Real.log (potential η ℓ T) ≥ -η * bestExpertLoss ℓ) (hη_ne : η ≠ 0) : η * (hedgeCumLoss η ℓ - bestExpertLoss ℓ) ≤ Real.log ↑N + η ^ 2 / 8 * ↑T := by
  nlinarith

private lemma hedge_regret_bound_tight_aux_hgoal {N T : Nat} [inst : NeZero N] (η : ℝ) (hη_pos : 0 < η) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (hstep : ∀ t : Fin T, Real.log (potential η ℓ (t.val + 1)) - Real.log (potential η ℓ t.val) ≤ -η * hedgeLoss η ℓ t + η ^ 2 / 8) (hsum : Real.log (potential η ℓ T) - Real.log (potential η ℓ 0) ≤ -η * hedgeCumLoss η ℓ + η ^ 2 / 8 * T) (hW0 : Real.log (potential η ℓ 0) = Real.log N) (hWT : Real.log (potential η ℓ T) ≥ -η * bestExpertLoss ℓ) (hη_ne : η ≠ 0) (hkey : η * (hedgeCumLoss η ℓ - bestExpertLoss ℓ) ≤ Real.log ↑N + η ^ 2 / 8 * ↑T) : hedgeCumLoss η ℓ - bestExpertLoss ℓ ≤ (Real.log ↑N + η ^ 2 / 8 * ↑T) / η := by
  rw [le_div_iff₀ hη_pos]; nlinarith

private lemma hedge_regret_bound_tight_aux_h_anon_1 {N T : Nat} [inst : NeZero N] (η : ℝ) (hη_pos : 0 < η) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (hstep : ∀ t : Fin T, Real.log (potential η ℓ (t.val + 1)) - Real.log (potential η ℓ t.val) ≤ -η * hedgeLoss η ℓ t + η ^ 2 / 8) (hsum : Real.log (potential η ℓ T) - Real.log (potential η ℓ 0) ≤ -η * hedgeCumLoss η ℓ + η ^ 2 / 8 * T) (hW0 : Real.log (potential η ℓ 0) = Real.log N) (hWT : Real.log (potential η ℓ T) ≥ -η * bestExpertLoss ℓ) (hη_ne : η ≠ 0) (hkey : η * (hedgeCumLoss η ℓ - bestExpertLoss ℓ) ≤ Real.log ↑N + η ^ 2 / 8 * ↑T) (hgoal : hedgeCumLoss η ℓ - bestExpertLoss ℓ ≤ (Real.log ↑N + η ^ 2 / 8 * ↑T) / η) : η ^ 2 / 8 * ↑T / η = η * ↑T / 8 := by
  rw [sq]; field_simp

theorem hedge_regret_bound_tight {N T : ℕ} [NeZero N] (η : ℝ)
    (hη_pos : 0 < η)
    (ℓ : LossSeq N T) (hℓ : ℓ.Valid) :
    regret η ℓ ≤ Real.log N / η + η * T / 8 := by
  -- Same potential proof as `hedge_regret_bound`, but the tight step bound
  -- avoids the extra `η ≤ 1` assumption and improves the constant.
  -- Same structure as hedge_regret_bound but using the tight step bound.
  -- Telescoping sum
  let hsum : Real.log (potential η ℓ T) - Real.log (potential η ℓ 0) ≤ -η * hedgeCumLoss η ℓ + η ^ 2 / 8 * T := (hedge_regret_bound_tight_aux_hsum η hη_pos ℓ hℓ (hedge_regret_bound_tight_aux_hstep η hη_pos ℓ hℓ))
  -- Use potential_zero and potential_ge_best_expert
  let hW0 : Real.log (potential η ℓ 0) = Real.log N := (hedge_regret_bound_tight_aux_hW0 η hη_pos ℓ hℓ (hedge_regret_bound_tight_aux_hstep η hη_pos ℓ hℓ) hsum)
  let hWT : Real.log (potential η ℓ T) ≥ -η * bestExpertLoss ℓ := (hedge_regret_bound_tight_aux_hWT η hη_pos ℓ hℓ (hedge_regret_bound_tight_aux_hstep η hη_pos ℓ hℓ) hsum hW0)
  -- Combine: η * regret ≤ log N + η²T/8
  unfold regret
  let hkey : η * (hedgeCumLoss η ℓ - bestExpertLoss ℓ) ≤ Real.log ↑N + η ^ 2 / 8 * ↑T := (hedge_regret_bound_tight_aux_hkey η hη_pos ℓ hℓ (hedge_regret_bound_tight_aux_hstep η hη_pos ℓ hℓ) hsum hW0 hWT (hedge_regret_bound_tight_aux_hη_ne η hη_pos ℓ hℓ (hedge_regret_bound_tight_aux_hstep η hη_pos ℓ hℓ) hsum hW0 hWT))
  let hgoal : hedgeCumLoss η ℓ - bestExpertLoss ℓ ≤ (Real.log ↑N + η ^ 2 / 8 * ↑T) / η := (hedge_regret_bound_tight_aux_hgoal η hη_pos ℓ hℓ (hedge_regret_bound_tight_aux_hstep η hη_pos ℓ hℓ) hsum hW0 hWT (hedge_regret_bound_tight_aux_hη_ne η hη_pos ℓ hℓ (hedge_regret_bound_tight_aux_hstep η hη_pos ℓ hℓ) hsum hW0 hWT) hkey)
  calc hedgeCumLoss η ℓ - bestExpertLoss ℓ
      ≤ (Real.log ↑N + η ^ 2 / 8 * ↑T) / η := hgoal
    _ = Real.log ↑N / η + η * ↑T / 8 := by
        rw [add_div, (hedge_regret_bound_tight_aux_h_anon_1 η hη_pos ℓ hℓ (hedge_regret_bound_tight_aux_hstep η hη_pos ℓ hℓ) hsum hW0 hWT (hedge_regret_bound_tight_aux_hη_ne η hη_pos ℓ hℓ (hedge_regret_bound_tight_aux_hstep η hη_pos ℓ hℓ) hsum hW0 hWT) hkey hgoal)]

/-! ## Theorem 1 Rate with the Tight Constant -/

/-- Learning rate optimizing the tight Hedge regret bound. -/
-- This balances `(log N) / η` and `ηT / 8`.
noncomputable def optimalEtaTight (N T : ℕ) : ℝ :=
  Real.sqrt (8 * Real.log N / T)

/-- With `η = √(8 log N / T)`, the tight Hedge bound gives
`regret ≤ √((T / 2) log N)`, matching the constant in the project writeup. -/
private lemma hedge_regret_tight_optimal_aux_hN_pos {N T : Nat} [inst : NeZero N] (hT : 0 < T) (hN : 1 < N) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (a : ℝ) (ha_def : a = log ↑N) (η : ℝ) (hη_def : η = optimalEtaTight N T) : (1 : ℝ) < ↑N := by
  exact_mod_cast hN

private lemma hedge_regret_tight_optimal_aux_ha_pos {N T : Nat} [inst : NeZero N] (hT : 0 < T) (hN : 1 < N) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (a : ℝ) (ha_def : a = log ↑N) (η : ℝ) (hη_def : η = optimalEtaTight N T) (hN_pos : (1 : ℝ) < ↑N) : 0 < log ↑N :=
  Real.log_pos hN_pos

private lemma hedge_regret_tight_optimal_aux_hT_pos {N T : Nat} [inst : NeZero N] (hT : 0 < T) (hN : 1 < N) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (a : ℝ) (ha_def : a = log ↑N) (η : ℝ) (hη_def : η = optimalEtaTight N T) (hN_pos : (1 : ℝ) < ↑N) (ha_pos : 0 < log ↑N) : (0 : ℝ) < ↑T :=
  Nat.cast_pos.mpr hT

private lemma hedge_regret_tight_optimal_aux_hη_pos {N T : Nat} [inst : NeZero N] (hT : 0 < T) (hN : 1 < N) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (a : ℝ) (ha_def : a = log ↑N) (η : ℝ) (hη_def : η = optimalEtaTight N T) (hN_pos : (1 : ℝ) < ↑N) (ha_pos : 0 < log ↑N) (hT_pos : (0 : ℝ) < ↑T) (hη_eq : η = Real.sqrt (8 * a / ↑T)) : 0 < η := by
  rw [hη_eq]
  exact Real.sqrt_pos.mpr (div_pos (by linarith) hT_pos)

private lemma hedge_regret_tight_optimal_aux_hη_sq {N T : Nat} [inst : NeZero N] (hT : 0 < T) (hN : 1 < N) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (a : ℝ) (ha_def : a = log ↑N) (η : ℝ) (hη_def : η = optimalEtaTight N T) (hN_pos : (1 : ℝ) < ↑N) (ha_pos : 0 < log ↑N) (hT_pos : (0 : ℝ) < ↑T) (hη_eq : η = Real.sqrt (8 * a / ↑T)) (hη_pos : 0 < η) : η ^ 2 = 8 * a / ↑T := by
  rw [hη_eq, sq_sqrt (le_of_lt (div_pos (by linarith) hT_pos))]

private lemma hedge_regret_tight_optimal_aux_hbound {N T : Nat} [inst : NeZero N] (hT : 0 < T) (hN : 1 < N) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (a : ℝ) (ha_def : a = log ↑N) (η : ℝ) (hη_def : η = optimalEtaTight N T) (hN_pos : (1 : ℝ) < ↑N) (ha_pos : 0 < log ↑N) (hT_pos : (0 : ℝ) < ↑T) (hη_eq : η = Real.sqrt (8 * a / ↑T)) (hη_pos : 0 < η) (hη_sq : η ^ 2 = 8 * a / ↑T) : regret η ℓ ≤ log ↑N / η + η * ↑T / 8 :=
  hedge_regret_bound_tight η hη_pos ℓ hℓ

private lemma hedge_regret_tight_optimal_aux_hη_ne {N T : Nat} [inst : NeZero N] (hT : 0 < T) (hN : 1 < N) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (a : ℝ) (ha_def : a = log ↑N) (η : ℝ) (hη_def : η = optimalEtaTight N T) (hN_pos : (1 : ℝ) < ↑N) (ha_pos : 0 < log ↑N) (hT_pos : (0 : ℝ) < ↑T) (hη_eq : η = Real.sqrt (8 * a / ↑T)) (hη_pos : 0 < η) (hη_sq : η ^ 2 = 8 * a / ↑T) (hbound : regret η ℓ ≤ log ↑N / η + η * ↑T / 8) (hlhs_nn : 0 ≤ a / η + η * ↑T / 8) : η ≠ 0 :=
  ne_of_gt hη_pos

private lemma hedge_regret_tight_optimal_aux_hηT {N T : Nat} [inst : NeZero N] (hT : 0 < T) (hN : 1 < N) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (a : ℝ) (ha_def : a = log ↑N) (η : ℝ) (hη_def : η = optimalEtaTight N T) (hN_pos : (1 : ℝ) < ↑N) (ha_pos : 0 < log ↑N) (hT_pos : (0 : ℝ) < ↑T) (hη_eq : η = Real.sqrt (8 * a / ↑T)) (hη_pos : 0 < η) (hη_sq : η ^ 2 = 8 * a / ↑T) (hbound : regret η ℓ ≤ log ↑N / η + η * ↑T / 8) (hlhs_nn : 0 ≤ a / η + η * ↑T / 8) (hη_ne : η ≠ 0) : η ^ 2 * ↑T = 8 * a := by
  rw [hη_sq]
  field_simp

private lemma hedge_regret_tight_optimal_aux_hprod {N T : Nat} [inst : NeZero N] (hT : 0 < T) (hN : 1 < N) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (a : ℝ) (ha_def : a = log ↑N) (η : ℝ) (hη_def : η = optimalEtaTight N T) (hN_pos : (1 : ℝ) < ↑N) (ha_pos : 0 < log ↑N) (hT_pos : (0 : ℝ) < ↑T) (hη_eq : η = Real.sqrt (8 * a / ↑T)) (hη_pos : 0 < η) (hη_sq : η ^ 2 = 8 * a / ↑T) (hbound : regret η ℓ ≤ log ↑N / η + η * ↑T / 8) (hlhs_nn : 0 ≤ a / η + η * ↑T / 8) (hη_ne : η ≠ 0) (hηT : η ^ 2 * ↑T = 8 * a) : (a / η + η * ↑T / 8) * η = 2 * a := by
  rw [add_mul, div_mul_cancel₀ a hη_ne]
  linarith [hηT]

private lemma hedge_regret_tight_optimal_aux_h1 {N T : Nat} [inst : NeZero N] (hT : 0 < T) (hN : 1 < N) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (a : ℝ) (ha_def : a = log ↑N) (η : ℝ) (hη_def : η = optimalEtaTight N T) (hN_pos : (1 : ℝ) < ↑N) (ha_pos : 0 < log ↑N) (hT_pos : (0 : ℝ) < ↑T) (hη_eq : η = Real.sqrt (8 * a / ↑T)) (hη_pos : 0 < η) (hη_sq : η ^ 2 = 8 * a / ↑T) (hbound : regret η ℓ ≤ log ↑N / η + η * ↑T / 8) (hlhs_nn : 0 ≤ a / η + η * ↑T / 8) (hη_ne : η ≠ 0) (hηT : η ^ 2 * ↑T = 8 * a) (hprod : (a / η + η * ↑T / 8) * η = 2 * a) : a / η + η * ↑T / 8 = 2 * a / η := by
  rw [eq_div_iff hη_ne]
  linarith [hprod]

private lemma hedge_regret_tight_optimal_aux_hsq {N T : Nat} [inst : NeZero N] (hT : 0 < T) (hN : 1 < N) (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (a : ℝ) (ha_def : a = log ↑N) (η : ℝ) (hη_def : η = optimalEtaTight N T) (hN_pos : (1 : ℝ) < ↑N) (ha_pos : 0 < log ↑N) (hT_pos : (0 : ℝ) < ↑T) (hη_eq : η = Real.sqrt (8 * a / ↑T)) (hη_pos : 0 < η) (hη_sq : η ^ 2 = 8 * a / ↑T) (hbound : regret η ℓ ≤ log ↑N / η + η * ↑T / 8) (hlhs_nn : 0 ≤ a / η + η * ↑T / 8) (hη_ne : η ≠ 0) (hηT : η ^ 2 * ↑T = 8 * a) (hprod : (a / η + η * ↑T / 8) * η = 2 * a) : (a / η + η * ↑T / 8) ^ 2 = ↑T / 2 * a := by
  rw [(hedge_regret_tight_optimal_aux_h1 hT hN ℓ hℓ a ha_def η hη_def hN_pos ha_pos hT_pos hη_eq hη_pos hη_sq hbound hlhs_nn hη_ne hηT hprod), div_pow]
  field_simp [hη_ne]
  nlinarith [hη_sq, sq_nonneg a]

theorem hedge_regret_tight_optimal {N T : ℕ} [NeZero N]
    (hT : 0 < T) (hN : 1 < N)
    (ℓ : LossSeq N T) (hℓ : ℓ.Valid) :
    regret (optimalEtaTight N T) ℓ ≤ Real.sqrt (T / 2 * Real.log N) := by
  -- Again the proof is algebra after applying the tight regret theorem.  The
  -- chosen learning rate makes the two terms in the bound equal.
  set a := Real.log ↑N with ha_def
  set η := optimalEtaTight N T with hη_def
  let hN_pos : (1 : ℝ) < ↑N := (hedge_regret_tight_optimal_aux_hN_pos hT hN ℓ hℓ a ha_def η hη_def)
  let ha_pos : 0 < log ↑N := (hedge_regret_tight_optimal_aux_ha_pos hT hN ℓ hℓ a ha_def η hη_def hN_pos)
  let hT_pos : (0 : ℝ) < ↑T := (hedge_regret_tight_optimal_aux_hT_pos hT hN ℓ hℓ a ha_def η hη_def hN_pos ha_pos)
  let hη_pos : 0 < η := (hedge_regret_tight_optimal_aux_hη_pos hT hN ℓ hℓ a ha_def η hη_def hN_pos ha_pos hT_pos (rfl))
  let hη_sq : η ^ 2 = 8 * a / ↑T := (hedge_regret_tight_optimal_aux_hη_sq hT hN ℓ hℓ a ha_def η hη_def hN_pos ha_pos hT_pos (rfl) hη_pos)
  let hbound : regret η ℓ ≤ log ↑N / η + η * ↑T / 8 := (hedge_regret_tight_optimal_aux_hbound hT hN ℓ hℓ a ha_def η hη_def hN_pos ha_pos hT_pos (rfl) hη_pos hη_sq)
  suffices hsuff : a / η + η * ↑T / 8 = Real.sqrt (↑T / 2 * a) by
    linarith
  let hlhs_nn : 0 ≤ a / η + η * ↑T / 8 := by positivity
  rw [← Real.sqrt_sq hlhs_nn]
  congr 1
  let hηT : η ^ 2 * ↑T = 8 * a := (hedge_regret_tight_optimal_aux_hηT hT hN ℓ hℓ a ha_def η hη_def hN_pos ha_pos hT_pos (rfl) hη_pos hη_sq hbound hlhs_nn (hedge_regret_tight_optimal_aux_hη_ne hT hN ℓ hℓ a ha_def η hη_def hN_pos ha_pos hT_pos (rfl) hη_pos hη_sq hbound hlhs_nn))
  let hsq : (a / η + η * ↑T / 8) ^ 2 = ↑T / 2 * a := (hedge_regret_tight_optimal_aux_hsq hT hN ℓ hℓ a ha_def η hη_def hN_pos ha_pos hT_pos (rfl) hη_pos hη_sq hbound hlhs_nn (hedge_regret_tight_optimal_aux_hη_ne hT hN ℓ hℓ a ha_def η hη_def hN_pos ha_pos hT_pos (rfl) hη_pos hη_sq hbound hlhs_nn) hηT (hedge_regret_tight_optimal_aux_hprod hT hN ℓ hℓ a ha_def η hη_def hN_pos ha_pos hT_pos (rfl) hη_pos hη_sq hbound hlhs_nn (hedge_regret_tight_optimal_aux_hη_ne hT hN ℓ hℓ a ha_def η hη_def hN_pos ha_pos hT_pos (rfl) hη_pos hη_sq hbound hlhs_nn) hηT))
  rw [hsq]
