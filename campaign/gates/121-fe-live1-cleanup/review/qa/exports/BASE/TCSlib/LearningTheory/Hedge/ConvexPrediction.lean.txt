/-
Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karim Abdel Sadek, Mark Bedaywi
-/

import Mathlib.Analysis.Convex.Jensen
import TCSlib.LearningTheory.Hedge.Regret

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Convex Prediction Bridge for Hedge

The exponentially weighted average forecaster of [CBL06, §2.1] in its original form: the
forecaster predicts the Hedge-weighted average of the experts' real-valued predictions and
pays a loss that is convex in the prediction.  Jensen's inequality compares this loss with
the expected expert loss of the abstract expert-setting Hedge in `Hedge.Basic`, so the
regret bounds of `Hedge.Regret` transfer; `hedgePrediction_regret_bound_tight` is the
statement that matches [CBL06, Thm 2.2] literally (for a prediction space `S ⊆ ℝ`).

## Main definitions

- `inducedLoss`: the expert-loss table obtained from expert predictions and outcomes.
- `hedgePrediction`, `hedgePredictionCumLoss`: the weighted-average prediction and its
  cumulative loss.

## Main results

- `hedgePrediction_mem`: Hedge's weighted-average prediction stays inside a convex decision
  set when all expert predictions are in that set.
- `hedgePrediction_loss_le_hedgeLoss`: Jensen's inequality shows the loss of the
  weighted-average prediction is at most Hedge's expected expert loss.
- `hedgePredictionCumLoss_le_hedgeCumLoss`: The actual cumulative prediction loss is
  bounded by the abstract Hedge cumulative loss.
- `hedgePrediction_regret_bound_tight`: Tight regret bound for actual weighted-average
  predictions via the Jensen bridge and the abstract Hedge theorem.
- `hedgePrediction_regret_tight_optimal`: Optimized-learning-rate regret bound for
  weighted-average predictions in a convex real decision set.

## References

* [CBL06] N. Cesa-Bianchi, G. Lugosi, *Prediction, Learning, and Games*, Cambridge
  University Press, 2006.
* [MRT18] M. Mohri, A. Rostamizadeh, A. Talwalkar, *Foundations of Machine Learning*,
  2nd ed., MIT Press, 2018.

Original formalization by Karim Abdel Sadek and Mark Bedaywi.
-/

open Real Finset BigOperators

/-! ## From Predictions to Expert Losses -/

/-- The loss sequence induced by expert predictions and outcomes: expert `i` at time `t`
receives the loss `ℓ(f_{i,t}, y_t)` of its own prediction against the realized outcome
[CBL06, §2.1].  This is the abstract loss table fed to the expert-setting Hedge. -/
noncomputable def inducedLoss {Ω : Type*} {N T : ℕ}
    (loss : ℝ → Ω → ℝ)
    (expertPred : Fin T → Fin N → ℝ)
    (outcome : Fin T → Ω) : LossSeq N T :=
  fun t i => loss (expertPred t i) (outcome t)

/-- The exponentially weighted average forecaster's prediction at round `t`: the weighted
average `Σ_i p_t(i) f_{i,t}` of the expert predictions using the Hedge distribution over the
induced expert losses [CBL06, §2.1].  This is the actual prediction made in the original
convex decision set.  The distribution depends only on losses before `t`, because
`hedgeDist` is defined from `cumLoss ... t`. -/
noncomputable def hedgePrediction {Ω : Type*} {N T : ℕ} [NeZero N]
    (η : ℝ)
    (loss : ℝ → Ω → ℝ)
    (expertPred : Fin T → Fin N → ℝ)
    (outcome : Fin T → Ω)
    (t : Fin T) : ℝ :=
  ∑ i : Fin N,
    hedgeDist η (inducedLoss loss expertPred outcome) t.val i * expertPred t i

/-- The cumulative loss `Σ_t ℓ(p̂_t, y_t)` of the forecaster's weighted-average predictions
`p̂_t = hedgePrediction … t` [CBL06, §2.1].  This is not the same object as `hedgeCumLoss`
in `Hedge.Basic`: here the predictions are averaged first and the real loss function is
applied to the average. -/
noncomputable def hedgePredictionCumLoss {Ω : Type*} {N T : ℕ} [NeZero N]
    (η : ℝ)
    (loss : ℝ → Ω → ℝ)
    (expertPred : Fin T → Fin N → ℝ)
    (outcome : Fin T → Ω) : ℝ :=
  ∑ t : Fin T, loss (hedgePrediction η loss expertPred outcome t) (outcome t)

/-- If every expert prediction lies in a convex set `S ⊆ ℝ`, then so does Hedge's
weighted-average prediction at every round: the Hedge weights are nonnegative and sum to
one, so convexity of `S` keeps the weighted average inside `S`. -/
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

/-- Jensen bridge: if all expert predictions lie in a convex set `S ⊆ ℝ` and the loss at
each round is convex in the prediction on `S`, then the loss of Hedge's weighted-average
prediction at round `t` is at most Hedge's expected expert loss
`Σ_i p_t(i) ℓ(f_{i,t}, y_t)` at that round [CBL06, proof of Thm 2.2 (Jensen step)].  The
left side is the real loss of the averaged prediction; the right side is the weighted average
of expert losses used in the abstract Hedge proof.  After expanding definitions this is
exactly Jensen's inequality (`ConvexOn.map_sum_le`) for the finite convex combination. -/
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

/-- Under the hypotheses of `hedgePrediction_loss_le_hedgeLoss`, the cumulative loss of
Hedge's weighted-average predictions is at most the cumulative expected expert loss
`hedgeCumLoss` of the abstract Hedge on the induced losses
[CBL06, proof of Thm 2.2 (Jensen step)]: sum the one-round Jensen inequality. -/
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

/-! ## CBL Theorem 2.2 in prediction space -/

/-- **Regret of the exponentially weighted average forecaster**: for a convex decision set
`S ⊆ ℝ`, expert predictions in `S`, round losses convex in the prediction on `S` and taking
values in `[0,1]` on the experts' predictions, and any `η > 0`, the cumulative loss of the
weighted-average predictions exceeds the cumulative loss of the best expert by at most
`(ln N)/η + ηT/8` [CBL06, Thm 2.2]; [MRT18, §8.2.4].  This is the statement that matches
CBL literally; it is the prediction-space counterpart of `hedge_regret_bound_tight`.
Deviation: the prediction space is a convex subset of `ℝ` rather than of a general vector
space, and boundedness of the loss is assumed only on the induced expert losses (`hvalid`).

Proof: Jensen (`hedgePredictionCumLoss_le_hedgeCumLoss`) compares the actual prediction
loss to the abstract Hedge loss, and `hedge_regret_bound_tight` on the induced loss table
controls the abstract Hedge loss against the best expert. -/
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

/-- **Regret of the exponentially weighted average forecaster at the optimal rate**: under
the hypotheses of `hedgePrediction_regret_bound_tight`, with `T > 0`, `N > 1`, and the
learning rate `η = optimalEtaTight N T = √(8 ln N / T)`, the cumulative loss of the
weighted-average predictions exceeds the cumulative loss of the best expert by at most
`√((T/2) ln N)` [CBL06, Cor 2.2].  This is the same Jensen bridge as above, applied to
`hedge_regret_tight_optimal` from `Hedge.Regret`. -/
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
