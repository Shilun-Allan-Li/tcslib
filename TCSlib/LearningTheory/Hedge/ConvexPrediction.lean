/-
Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karim Abdel Sadek, Mark Bedaywi
-/

import TCSlib.LearningTheory.Hedge

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

open Real Finset BigOperators

/-!
# Convex Prediction Bridge for Hedge

## Main results

- `hedgePrediction_mem`: Hedge's weighted-average prediction stays inside a convex decision set when all expert predictions are in that set.
- `hedgePrediction_loss_le_hedgeLoss`: Jensen's inequality shows the loss of the weighted-average prediction is at most Hedge's expected expert loss.
- `hedgePredictionCumLoss_le_hedgeCumLoss`: The actual cumulative prediction loss is bounded by the abstract Hedge cumulative loss.
- `hedgePrediction_regret_bound_tight`: Tight regret bound for actual weighted-average predictions via the Jensen bridge and the abstract Hedge theorem.
- `hedgePrediction_regret_tight_optimal`: Optimized-learning-rate regret bound for weighted-average predictions in a convex real decision set.

## References

- Original formalization by Karim Abdel Sadek, Mark Bedaywi
-/

/-! ## From Predictions to Expert Losses -/

/-- The loss sequence induced by expert predictions and outcomes. -/
-- Expert `i` at time `t` receives the loss of its own prediction against the
-- realized outcome at time `t`.  This is the abstract loss table used by Hedge.
noncomputable def inducedLoss {Ω : Type*} {N T : ℕ}
    (loss : ℝ → Ω → ℝ)
    (expertPred : Fin T → Fin N → ℝ)
    (outcome : Fin T → Ω) : LossSeq N T :=
  fun t i => loss (expertPred t i) (outcome t)

/-- Hedge's prediction in the original decision space: the weighted average of
the expert predictions using the Hedge distribution over induced expert losses.

The distribution depends only on losses before `t`, because `hedgeDist` is
defined from `cumLoss ... t`. -/
-- This is the actual prediction made in the original convex decision set:
-- take the Hedge weights from the induced loss table and average the experts'
-- predictions at the current round.
noncomputable def hedgePrediction {Ω : Type*} {N T : ℕ} [NeZero N]
    (η : ℝ)
    (loss : ℝ → Ω → ℝ)
    (expertPred : Fin T → Fin N → ℝ)
    (outcome : Fin T → Ω)
    (t : Fin T) : ℝ :=
  ∑ i : Fin N,
    hedgeDist η (inducedLoss loss expertPred outcome) t.val i * expertPred t i

/-- The actual cumulative loss of Hedge's weighted-average predictions. -/
-- This is not the same object as `hedgeCumLoss` in `Hedge.lean`.  Here we first
-- average the predictions, then apply the real loss function to that average.
noncomputable def hedgePredictionCumLoss {Ω : Type*} {N T : ℕ} [NeZero N]
    (η : ℝ)
    (loss : ℝ → Ω → ℝ)
    (expertPred : Fin T → Fin N → ℝ)
    (outcome : Fin T → Ω) : ℝ :=
  ∑ t : Fin T, loss (hedgePrediction η loss expertPred outcome t) (outcome t)

/-- Hedge's weighted-average prediction remains in a convex decision set when all
expert predictions are in that set. -/
-- The Hedge weights are nonnegative and sum to one, so convexity of `S` keeps
-- the weighted average inside `S`.
lemma hedgePrediction_mem {Ω : Type*} {N T : ℕ} [NeZero N]
    {S : Set ℝ} (hS : Convex ℝ S)
    (η : ℝ)
    (loss : ℝ → Ω → ℝ)
    (expertPred : Fin T → Fin N → ℝ)
    (outcome : Fin T → Ω)
    (hexpert : ∀ t i, expertPred t i ∈ S)
    (t : Fin T) :
    hedgePrediction η loss expertPred outcome t ∈ S := by
  simpa [hedgePrediction, smul_eq_mul] using
    hS.sum_mem (t := Finset.univ)
      (w := fun i : Fin N => hedgeDist η (inducedLoss loss expertPred outcome) t.val i)
      (z := fun i : Fin N => expertPred t i)
      (fun i _ => hedgeDist_nonneg η (inducedLoss loss expertPred outcome) t.val i)
      (by simpa using hedgeDist_sum η (inducedLoss loss expertPred outcome) t.val)
      (fun i _ => hexpert t i)

/-- Jensen bridge: if the round loss is convex in the prediction, then the loss
of Hedge's weighted-average prediction is at most Hedge's expected expert loss. -/
-- This is the key bridge.  The left side is the real loss of the averaged
-- prediction; the right side is the weighted average of expert losses used in
-- the abstract Hedge proof.
lemma hedgePrediction_loss_le_hedgeLoss {Ω : Type*} {N T : ℕ} [NeZero N]
    {S : Set ℝ} (hS : Convex ℝ S)
    (η : ℝ)
    (loss : ℝ → Ω → ℝ)
    (expertPred : Fin T → Fin N → ℝ)
    (outcome : Fin T → Ω)
    (hexpert : ∀ t i, expertPred t i ∈ S)
    (hloss_conv : ∀ t : Fin T, ConvexOn ℝ S (fun x => loss x (outcome t)))
    (t : Fin T) :
    loss (hedgePrediction η loss expertPred outcome t) (outcome t)
      ≤ hedgeLoss η (inducedLoss loss expertPred outcome) t := by
  -- After expanding definitions, this is exactly Jensen's inequality for a
  -- convex function evaluated at the finite convex combination of expert
  -- predictions.
  have hmem : hedgePrediction η loss expertPred outcome t ∈ S :=
    hedgePrediction_mem hS η loss expertPred outcome hexpert t
  simpa [hedgePrediction, hedgeLoss, inducedLoss, smul_eq_mul] using
    (hloss_conv t).map_sum_le (t := Finset.univ)
      (w := fun i : Fin N => hedgeDist η (inducedLoss loss expertPred outcome) t.val i)
      (p := fun i : Fin N => expertPred t i)
      (fun i _ => hedgeDist_nonneg η (inducedLoss loss expertPred outcome) t.val i)
      (by simpa using hedgeDist_sum η (inducedLoss loss expertPred outcome) t.val)
      (fun i _ => hexpert t i)

/-- The actual cumulative loss of Hedge's predictions is bounded by the expected
expert-loss cumulative quantity used in `Hedge.lean`. -/
-- Summing the one-round Jensen inequality gives the cumulative comparison.
lemma hedgePredictionCumLoss_le_hedgeCumLoss {Ω : Type*} {N T : ℕ} [NeZero N]
    {S : Set ℝ} (hS : Convex ℝ S)
    (η : ℝ)
    (loss : ℝ → Ω → ℝ)
    (expertPred : Fin T → Fin N → ℝ)
    (outcome : Fin T → Ω)
    (hexpert : ∀ t i, expertPred t i ∈ S)
    (hloss_conv : ∀ t : Fin T, ConvexOn ℝ S (fun x => loss x (outcome t))) :
    hedgePredictionCumLoss η loss expertPred outcome
      ≤ hedgeCumLoss η (inducedLoss loss expertPred outcome) := by
  exact Finset.sum_le_sum fun t _ =>
    hedgePrediction_loss_le_hedgeLoss hS η loss expertPred outcome hexpert hloss_conv t

/-! ## The Writeup-Style Regret Bound -/

/-- The tight Hedge regret bound for actual weighted-average predictions in a
convex real decision set.  This is the prediction-space counterpart of
`hedge_regret_bound_tight`: the existing expert-loss regret theorem is applied
to the induced expert losses, while convexity/Jensen moves the left-hand side
back to the original decision space. -/
-- The proof has two ingredients: Jensen compares actual prediction loss to
-- abstract Hedge loss, and `hedge_regret_bound_tight` controls the abstract
-- Hedge loss against the best expert.
theorem hedgePrediction_regret_bound_tight {Ω : Type*} {N T : ℕ} [NeZero N]
    {S : Set ℝ} (hS : Convex ℝ S)
    (η : ℝ) (hη_pos : 0 < η)
    (loss : ℝ → Ω → ℝ)
    (expertPred : Fin T → Fin N → ℝ)
    (outcome : Fin T → Ω)
    (hexpert : ∀ t i, expertPred t i ∈ S)
    (hloss_conv : ∀ t : Fin T, ConvexOn ℝ S (fun x => loss x (outcome t)))
    (hvalid : (inducedLoss loss expertPred outcome).Valid) :
    hedgePredictionCumLoss η loss expertPred outcome
        - bestExpertLoss (inducedLoss loss expertPred outcome)
      ≤ Real.log N / η + η * T / 8 := by
  -- First move from real prediction loss to the abstract expected expert loss.
  have hcum :=
    hedgePredictionCumLoss_le_hedgeCumLoss hS η loss expertPred outcome hexpert hloss_conv
  -- Then use the already-proved Hedge regret theorem on the induced loss table.
  have hreg :=
    hedge_regret_bound_tight η hη_pos (inducedLoss loss expertPred outcome) hvalid
  unfold regret at hreg
  linarith

/-- Optimized tight regret bound for actual weighted-average predictions. -/
-- This is the same bridge as above, but using the optimized learning rate from
-- `Hedge.lean`.
theorem hedgePrediction_regret_tight_optimal {Ω : Type*} {N T : ℕ} [NeZero N]
    {S : Set ℝ} (hS : Convex ℝ S)
    (hT : 0 < T) (hN : 1 < N)
    (loss : ℝ → Ω → ℝ)
    (expertPred : Fin T → Fin N → ℝ)
    (outcome : Fin T → Ω)
    (hexpert : ∀ t i, expertPred t i ∈ S)
    (hloss_conv : ∀ t : Fin T, ConvexOn ℝ S (fun x => loss x (outcome t)))
    (hvalid : (inducedLoss loss expertPred outcome).Valid) :
    hedgePredictionCumLoss (optimalEtaTight N T) loss expertPred outcome
        - bestExpertLoss (inducedLoss loss expertPred outcome)
      ≤ Real.sqrt (T / 2 * Real.log N) := by
  -- Jensen gives the cumulative comparison for the optimized `η`.
  have hcum :=
    hedgePredictionCumLoss_le_hedgeCumLoss hS (optimalEtaTight N T)
      loss expertPred outcome hexpert hloss_conv
  -- The optimized regret bound itself is imported from the abstract Hedge file.
  have hreg :=
    hedge_regret_tight_optimal hT hN (inducedLoss loss expertPred outcome) hvalid
  unfold regret at hreg
  linarith
