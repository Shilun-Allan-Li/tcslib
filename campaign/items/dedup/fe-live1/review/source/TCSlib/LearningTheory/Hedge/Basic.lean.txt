/-
Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karim Abdel Sadek, Mark Bedaywi
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Field

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Hedge Algorithm: Definitions and Potential Lemmas

The Hedge algorithm of Freund–Schapire [FS97, §2] (with `β = e^{-η}`), equivalently the
exponentially weighted average forecaster of Cesa-Bianchi–Lugosi [CBL06, §2.1], in the
*expert* setting: at each round the learner plays a distribution over `N` experts and pays
the expected loss.  This file has the definitions and the potential-function lemmas that
`Hedge.Regret` telescopes into the regret bounds.

## Main definitions

- `LossSeq`, `LossSeq.Valid`: loss sequences over `N` experts and `T` rounds, with losses
  in `[0,1]`.
- `cumLoss`, `hedgeWeight`, `potential`, `hedgeDist`: cumulative losses, Hedge weights,
  the potential `W_t`, and the Hedge distribution.
- `hedgeLoss`, `hedgeCumLoss`, `bestExpertLoss`, `regret`: expected per-round loss,
  cumulative loss, best-expert loss, and regret.

## Main results

- `potential_ratio_le`: the per-round potential ratio `W_{t+1}/W_t` is at most
  `1 - (1 - e^{-η}) · hedgeLoss`.
- `log_potential_step`: per-round log-potential step bound.
- `potential_ge_best_expert`: `W_T ≥ exp(-η · bestExpertLoss)`.
- `hedgeDist_sum`, `hedgeDist_nonneg`, `hedgeLoss_le_one`, `hedgeLoss_nonneg`: basic
  properties of the Hedge distribution and loss.

## References

* [CBL06] N. Cesa-Bianchi, G. Lugosi, *Prediction, Learning, and Games*, Cambridge
  University Press, 2006.
* [FS97] Y. Freund, R. E. Schapire, "A decision-theoretic generalization of on-line
  learning and an application to boosting", *J. Comput. Syst. Sci.* 55(1):119–139, 1997.

Original formalization by Karim Abdel Sadek and Mark Bedaywi.
-/

open Real Finset BigOperators

/-! ## Expert Setting

We fix N experts and T rounds. At each round t, the adversary reveals
a loss vector ℓ_t : Fin N → [0,1]. The learner picks a distribution
over experts and incurs the expected loss.

The code represents the whole realized trajectory as `LossSeq N T`.  This is
the right level of abstraction for the algebraic Hedge proof: each round only
uses the current loss vector and the weights computed from previous losses.
-/

/-- The type of loss sequences over `N` experts and `T` rounds: a whole `T × N` trajectory,
`ℓ t i` being the loss of expert `i` at round `t` [CBL06, §2.1].  The `[0, 1]` range
condition is kept as a separate predicate (`LossSeq.Valid`) instead of being built into the
type, which keeps the algebraic definitions simple. -/
def LossSeq (N T : ℕ) := Fin T → Fin N → ℝ

/-- A loss sequence is valid if every loss `ℓ t i` lies in the interval `[0,1]` [CBL06, §2.1]. -/
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

/-- The cumulative loss `L_t(i) = ∑_{s < t} ℓ_s(i)` of expert `i` through the first `t` rounds
[FS97, §2]; [CBL06, §2.1].  This sums exactly the rounds whose index is less than `t`. -/
noncomputable def cumLoss {N T : ℕ} (ℓ : LossSeq N T) (t : ℕ) (i : Fin N) : ℝ :=
  ((Finset.univ (α := Fin T)).filter (fun s => s.val < t)).sum (fun s => ℓ s i)

/-- The unnormalized Hedge weight `w_t(i) = exp(-η · L_t(i))` of expert `i` at round `t`
[FS97, §2 (Hedge(β) with `β = e^{-η}`)]; [CBL06, §2.1].  Experts with smaller cumulative
loss get larger exponential weight. -/
noncomputable def hedgeWeight {N T : ℕ} (η : ℝ) (ℓ : LossSeq N T) (t : ℕ) (i : Fin N) : ℝ :=
  Real.exp (-η * cumLoss ℓ t i)

/-- The potential `W_t = ∑_i w_t(i)`, the sum of the unnormalized weights at round `t`
[FS97, §2]; [CBL06, proof of Thm 2.2].  The potential is the object we track: its one-step
upper bound gives Hedge's cumulative loss, while its final lower bound sees the best expert. -/
noncomputable def potential {N T : ℕ} (η : ℝ) (ℓ : LossSeq N T) (t : ℕ) : ℝ :=
  ∑ i : Fin N, hedgeWeight η ℓ t i

/-- The Hedge distribution at round `t`: the normalized weights `p_t(i) = w_t(i) / W_t`
[FS97, §2]; [CBL06, §2.1]. -/
noncomputable def hedgeDist {N T : ℕ} (η : ℝ) (ℓ : LossSeq N T) (t : ℕ) (i : Fin N) : ℝ :=
  hedgeWeight η ℓ t i / potential η ℓ t

/-- The expected loss `∑_i p_t(i) ℓ_t(i)` of the learner at round `t` under the Hedge
distribution [FS97, §2]; [CBL06, §2.1].  Deviation: the loss is linear in the distribution
(the expert setting of [FS97]), not CBL's convex loss of a weighted-average prediction; the
latter is recovered in `Hedge.ConvexPrediction` via Jensen. -/
noncomputable def hedgeLoss {N T : ℕ} (η : ℝ) (ℓ : LossSeq N T) (t : Fin T) : ℝ :=
  ∑ i : Fin N, hedgeDist η ℓ t.val i * ℓ t i

/-- The cumulative expected loss `∑_{t < T} ∑_i p_t(i) ℓ_t(i)` of Hedge over the `T` rounds
[FS97, §2]; [CBL06, §2.1]. -/
noncomputable def hedgeCumLoss {N T : ℕ} (η : ℝ) (ℓ : LossSeq N T) : ℝ :=
  ∑ t : Fin T, hedgeLoss η ℓ t

/-- The cumulative loss `min_i L_T(i)` of the best expert in hindsight [FS97, §2];
[CBL06, §2.1].  This is an infimum over a finite nonempty set of experts, so later we can
choose an expert attaining it when lower-bounding the final potential. -/
noncomputable def bestExpertLoss {N T : ℕ} (ℓ : LossSeq N T) : ℝ :=
  ⨅ i : Fin N, cumLoss ℓ T i

/-- The regret of Hedge: its cumulative expected loss minus the cumulative loss of the best
expert in hindsight [CBL06, §2.1]; [FS97, §2]. -/
noncomputable def regret {N T : ℕ} (η : ℝ) (ℓ : LossSeq N T) : ℝ :=
  hedgeCumLoss η ℓ - bestExpertLoss ℓ

/-! ## Key Lemmas -/

/-!
The lemmas in this section are the mechanics of the potential proof.  The main
work is to relate `W_{t+1} / W_t` to the current expected loss, then telescope
the resulting logarithmic inequality over all rounds.
-/

/-- The potential at time `0` equals `N`: every cumulative loss is `0`, so every weight is `1`.
-/
lemma potential_zero {N T : ℕ} [NeZero N] (η : ℝ) (ℓ : LossSeq N T) :
    potential η ℓ 0 = N := by
  simp only [potential, hedgeWeight, cumLoss]
  have hfilt : ∀ i : Fin N, ((Finset.univ (α := Fin T)).filter (fun s => s.val < 0)).sum
      (fun s => ℓ s i) = 0 := by
    intro i
    apply Finset.sum_eq_zero
    intro s hs
    simp at hs
  simp only [hfilt, mul_zero, exp_zero, Finset.sum_const, Finset.card_fin]
  simp

/-- Every Hedge weight is strictly positive, being an exponential. -/
lemma hedgeWeight_pos {N T : ℕ} (η : ℝ) (ℓ : LossSeq N T) (t : ℕ) (i : Fin N) :
    0 < hedgeWeight η ℓ t i := by
  exact exp_pos _

/-- The potential is strictly positive: it is a nonempty sum of positive weights. -/
lemma potential_pos {N T : ℕ} [NeZero N] (η : ℝ) (ℓ : LossSeq N T) (t : ℕ) :
    0 < potential η ℓ t := by
  apply Finset.sum_pos
  · intro i _
    exact hedgeWeight_pos η ℓ t i
  · exact Finset.univ_nonempty

/-- For `x ∈ [0,1]` and `η > 0`, `exp(-ηx) ≤ 1 - (1 - exp(-η)) x`: the exponential lies below
the chord joining its values at `-η` and `0`.  This is the elementary bound
`β^x ≤ 1 - (1 - β) x` of [FS97, §2.1, Eq. (3) (proof of Lemma 1)] with `β = e^{-η}`; it
replaces Hoeffding's lemma in the weak regret bound. -/
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

/-- The cumulative loss through `t + 1` rounds is the cumulative loss through `t` rounds plus
the loss at round `t`: `L_{t+1}(i) = L_t(i) + ℓ_t(i)`. -/
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

/-- At the final horizon `T`, the cumulative loss of expert `i` is the sum of its losses over
all `T` rounds. -/
lemma cumLoss_horizon {N T : ℕ} (ℓ : LossSeq N T) (i : Fin N) :
    cumLoss ℓ T i = ∑ t : Fin T, ℓ t i := by
  simp only [cumLoss]
  congr 1
  ext t
  simp

/-- The weight update is multiplicative: `w_{t+1}(i) = w_t(i) · exp(-η · ℓ_t(i))` [FS97, §2]. -/
lemma hedgeWeight_succ {N T : ℕ} (η : ℝ) (ℓ : LossSeq N T) (t : Fin T) (i : Fin N) :
    hedgeWeight η ℓ (t.val + 1) i = hedgeWeight η ℓ t.val i * Real.exp (-η * ℓ t i) := by
  simp only [hedgeWeight, cumLoss_succ]
  ring_nf
  rw [← exp_add]
  ring_nf

/-- The Hedge distribution at any round is a probability vector: its coordinates sum to `1`. -/
lemma hedgeDist_sum {N T : ℕ} [NeZero N] (η : ℝ) (ℓ : LossSeq N T) (t : ℕ) :
    ∑ i : Fin N, hedgeDist η ℓ t i = 1 := by
  -- Normalization by the positive potential turns weights into a probability
  -- distribution.
  simp only [hedgeDist]
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (potential_pos η ℓ t))

/-- One-step potential ratio bound: for a valid loss sequence and `η > 0`,
`W_{t+1} / W_t ≤ 1 - (1 - exp(-η)) · (p_t · ℓ_t)`, where `p_t · ℓ_t` is Hedge's expected loss
at round `t` [CBL06, proof of Thm 2.2]; [FS97, §2.1, Eq. (4) (proof of Lemma 1)].  Deviation:
each term is bounded with the elementary chord inequality `exp_neg_le_linear` instead of
Hoeffding's lemma, which is why the downstream weak bound has `ηT/2` rather than `ηT/8`.
(An earlier docstring called this "CBL Lemma 2.2"; that lemma is Hoeffding's lemma, used
only in the tight bound.)  The hypothesis `ht` is not used.

**Proof sketch.** Multiply through by `W_t > 0`.
Step 1: by the multiplicative weight update, `W_{t+1} = ∑_i w_t(i) exp(-η ℓ_t(i))`.
Step 2: bound each summand by `w_t(i) (1 - (1 - e^{-η}) ℓ_t(i))` using `exp_neg_le_linear`
on `ℓ_t(i) ∈ [0,1]`.
Step 3: sum the bounds and identify `∑_i w_t(i) (1 - c ℓ_t(i)) = (1 - c · hedgeLoss) · W_t`
with `c = 1 - e^{-η}`, using `hedgeLoss = (∑_i w_t(i) ℓ_t(i)) / W_t`. -/
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
  -- Step 1: clear the denominator and rewrite `W_{t+1}` by the multiplicative weight update
  rw [div_le_iff₀ hWt]
  -- Goal: potential η ℓ (t+1) ≤ (1 - (1 - exp(-η)) * hedgeLoss η ℓ t) * potential η ℓ t
  -- W_{t+1} = ∑ w_t(i) * exp(-η * ℓ_t(i))
  have hW_succ : potential η ℓ (t.val + 1) =
      ∑ i : Fin N, hedgeWeight η ℓ t.val i * Real.exp (-η * ℓ t i) := by
    simp only [potential]; congr 1; ext i; exact hedgeWeight_succ η ℓ t i
  rw [hW_succ]
  -- Step 2: bound each summand with `exp_neg_le_linear`
  have hbound : ∀ i : Fin N,
      hedgeWeight η ℓ t.val i * Real.exp (-η * ℓ t i) ≤
      hedgeWeight η ℓ t.val i * (1 - (1 - Real.exp (-η)) * ℓ t i) := by
    intro i
    exact mul_le_mul_of_nonneg_left (exp_neg_le_linear hη (hℓ t i).1 (hℓ t i).2)
      (hedgeWeight_pos η ℓ t.val i).le
  -- Step 3: sum the bounds and show RHS = (1 - c * hedgeLoss) * W
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

/-- One-step log-potential bound: for a valid loss sequence and `η > 0`,
`ln W_{t+1} - ln W_t ≤ -(1 - exp(-η)) · (p_t · ℓ_t)` [CBL06, proof of Thm 2.2].  This is the
additive form of `potential_ratio_le`, obtained from `ln x ≤ x - 1`; it is what telescopes
over the rounds in `Hedge.Regret`.  The hypothesis `ht` is only forwarded to
`potential_ratio_le`, which does not use it. -/
lemma log_potential_step {N T : ℕ} [NeZero N] (η : ℝ) (hη : 0 < η)
    (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (t : Fin T) (ht : t.val + 1 ≤ T) :
    Real.log (potential η ℓ (t.val + 1)) - Real.log (potential η ℓ t.val)
      ≤ -(1 - Real.exp (-η)) * hedgeLoss η ℓ t := by
  -- Convert the multiplicative potential-ratio bound into an additive
  -- log-potential bound.  This is what will telescope across time.
  have hWt := potential_pos η ℓ t.val
  have hWt1 := potential_pos η ℓ (t.val + 1)
  rw [← Real.log_div (ne_of_gt hWt1) (ne_of_gt hWt)]
  have hratio := potential_ratio_le η hη ℓ hℓ t ht
  set c := (1 : ℝ) - Real.exp (-η)
  -- The ratio is positive (from hratio and the fact W_{t+1}/W_t > 0)
  have hratio_pos : 0 < potential η ℓ (t.val + 1) / potential η ℓ t.val :=
    div_pos hWt1 hWt
  have h1mc_pos : 0 < 1 - c * hedgeLoss η ℓ t := by linarith
  -- log(ratio) ≤ log(1 - c * hedgeLoss) ≤ (1 - c * hedgeLoss) - 1 = -c * hedgeLoss
  -- using log x ≤ x - 1 for x > 0.
  calc Real.log (potential η ℓ (t.val + 1) / potential η ℓ t.val)
      ≤ Real.log (1 - c * hedgeLoss η ℓ t) := by
        exact Real.log_le_log hratio_pos hratio
    _ ≤ (1 - c * hedgeLoss η ℓ t) - 1 := Real.log_le_sub_one_of_pos h1mc_pos
    _ = -(1 - Real.exp (-η)) * hedgeLoss η ℓ t := by ring

/-- For `t ≥ 0`, `exp(-t) ≤ 1 - t + t²/2` (the second-order upper Taylor bound for `exp(-t)`).
Proof idea: multiply by `exp t > 0`; from the lower Taylor bound `1 + t + t²/2 ≤ exp t` we get
`exp(t) (1 - t + t²/2) ≥ (1 + t + t²/2)(1 - t + t²/2) = 1 + t⁴/4 ≥ 1`. -/
lemma exp_neg_le_quadratic {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-t) ≤ 1 - t + t ^ 2 / 2 := by
  -- We prove the bound by multiplying both sides by `exp t > 0` and using the
  -- standard lower Taylor bound for `exp t`.
  have he : (0 : ℝ) < Real.exp t := exp_pos t
  have hq : (0 : ℝ) < 1 - t + t ^ 2 / 2 := by nlinarith [sq_nonneg t]
  -- exp(t) ≥ 1 + t + t²/2
  have hquad := quadratic_le_exp_of_nonneg ht
  -- (1 + t + t²/2)(1 - t + t²/2) = 1 + t⁴/4 ≥ 1
  -- So exp(t) * (1 - t + t²/2) ≥ (1 + t + t²/2)(1 - t + t²/2) ≥ 1
  have key : 1 ≤ Real.exp t * (1 - t + t ^ 2 / 2) := by
    have : (1 + t + t ^ 2 / 2) * (1 - t + t ^ 2 / 2) = 1 + t ^ 4 / 4 := by ring
    nlinarith [sq_nonneg (t ^ 2), mul_le_mul_of_nonneg_right hquad hq.le]
  -- exp(-t) = (exp t)⁻¹ ≤ 1 - t + t²/2
  rw [exp_neg]
  exact le_of_mul_le_mul_left (by nlinarith [mul_inv_cancel₀ he.ne']) he

/-- For `η > 0`, `1 - exp(-η) ≥ η - η²/2`: the rearranged form of `exp_neg_le_quadratic`.
This is the relaxation of the chord coefficient `1 - e^{-η}` that turns the per-step bound
`log_potential_step` into `-η · hedgeLoss + η²/2` in the weak regret bound. -/
lemma one_sub_exp_neg_ge {η : ℝ} (hη : 0 < η) :
    1 - Real.exp (-η) ≥ η - η ^ 2 / 2 := by
  -- Rearranged form of the previous quadratic upper bound on `exp (-η)`.
  have h := exp_neg_le_quadratic hη.le
  linarith

/-- Lower bound on the final potential by the best expert: `W_T ≥ exp(-η · min_i L_T(i))`,
since the sum of the final weights is at least the single largest weight
[CBL06, proof of Thm 2.2]; [FS97, §2.1, proof of Thm 2].  The hypothesis `hη` is not used. -/
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

/-- Every coordinate of the Hedge distribution is nonnegative. -/
lemma hedgeDist_nonneg {N T : ℕ} [NeZero N] (η : ℝ) (ℓ : LossSeq N T) (t : ℕ) (i : Fin N) :
    0 ≤ hedgeDist η ℓ t i :=
  div_nonneg (hedgeWeight_pos η ℓ t i).le (potential_pos η ℓ t).le

/-- For a valid loss sequence, Hedge's expected loss at each round is at most `1`. -/
lemma hedgeLoss_le_one {N T : ℕ} [NeZero N] (η : ℝ) (ℓ : LossSeq N T) (hℓ : ℓ.Valid)
    (t : Fin T) : hedgeLoss η ℓ t ≤ 1 := by
  -- A convex combination of losses in `[0, 1]` is at most `1`.
  have hsum : hedgeLoss η ℓ t ≤ ∑ i : Fin N, hedgeDist η ℓ t.val i * 1 := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (hℓ t i).2 (hedgeDist_nonneg η ℓ t.val i)
  simp only [mul_one] at hsum
  linarith [hedgeDist_sum η ℓ t.val]

/-- For a valid loss sequence, Hedge's expected loss at each round is nonnegative. -/
lemma hedgeLoss_nonneg {N T : ℕ} [NeZero N] (η : ℝ) (ℓ : LossSeq N T) (hℓ : ℓ.Valid)
    (t : Fin T) : 0 ≤ hedgeLoss η ℓ t := by
  -- A convex combination of nonnegative losses is nonnegative.
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (hedgeDist_nonneg η ℓ t.val i) (hℓ t i).1
