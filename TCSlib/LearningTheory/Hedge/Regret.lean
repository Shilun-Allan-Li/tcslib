/-
Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karim Abdel Sadek, Mark Bedaywi
-/
import TCSlib.LearningTheory.Hedge.Basic
import TCSlib.LearningTheory.Hedge.Hoeffding

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Hedge Algorithm: No-Regret Guarantee

The regret bounds for Hedge in the expert setting: the potential argument of
[CBL06, Thm 2.2] / [FS97, §2.1 (Lemma 1, Thm 2)] run twice, once with the elementary chord
bound (constant `ηT/2`, stated with `η ≤ 1`) and once with Hoeffding's lemma (CBL's
constant `ηT/8`, any `η > 0`), plus the optimized learning rates of [CBL06, Cor 2.2].

## Main definitions

- `optimalEta`: the learning rate `√(2 ln N / T)` optimizing the weak bound.
- `optimalEtaTight`: the learning rate `√(8 ln N / T)` optimizing the tight bound.

## Main results

- `log_potential_telescope`, `regret_le_of_log_potential_step`: the shared potential
  argument — telescoping the per-round log-potential bound gives
  regret ≤ (ln N)/η + cT/η.
- `optimalEta_balance`: at η = √(c·a/T) the two terms a/η and ηT/c balance to √(4aT/c).
- `hedge_regret_bound`: For any valid loss sequence with N experts, T rounds, and
  η ∈ (0,1], the regret of Hedge is at most (ln N)/η + ηT/2.
- `hedge_regret_bound_tight`: For any valid loss sequence with N experts, T rounds, and
  η > 0, the regret of Hedge is at most (ln N)/η + ηT/8.
- `hedge_regret_optimal`: With optimal η = √(2 ln N / T), regret ≤ √(2 T ln N).
- `hedge_regret_tight_optimal`: With η = √(8 log N / T), the tight Hedge bound gives
  regret ≤ √((T/2) log N).
- `hedge_no_regret`: Average regret ≤ √(2 ln N / T), which tends to 0 as T → ∞.
- `hoeffding_lemma`: For p ∈ [0,1] and any h ∈ ℝ, ln((1-p) + p·eʰ) ≤ p·h + h²/8.

## References

* [CBL06] N. Cesa-Bianchi, G. Lugosi, *Prediction, Learning, and Games*, Cambridge
  University Press, 2006.
* [FS97] Y. Freund, R. E. Schapire, "A decision-theoretic generalization of on-line
  learning and an application to boosting", *J. Comput. Syst. Sci.* 55(1):119–139, 1997.
* [MRT18] M. Mohri, A. Rostamizadeh, A. Talwalkar, *Foundations of Machine Learning*,
  2nd ed., MIT Press, 2018.

Original formalization by Karim Abdel Sadek and Mark Bedaywi.
-/

open Real Finset BigOperators

/-! ## Shared potential argument -/

/-- Telescoping the one-step changes of the log potential: summing
`log W_{t+1} - log W_t` over the `T` rounds gives `log W_T - log W_0`.  Pure bookkeeping
(the sum over `Fin T` is rewritten as a sum over `range T` and `Finset.sum_range_sub`
applies); no textbook counterpart. -/
lemma log_potential_telescope {N T : ℕ} (η : ℝ) (ℓ : LossSeq N T) :
    ∑ t : Fin T, (Real.log (potential η ℓ (t.val + 1)) - Real.log (potential η ℓ t.val)) =
      Real.log (potential η ℓ T) - Real.log (potential η ℓ 0) := by
  set f := fun n => Real.log (potential η ℓ n)
  show ∑ t : Fin T, (f (t.val + 1) - f t.val) = f T - f 0
  conv_lhs => arg 2; ext t; rw [show t.val = (t : ℕ) from rfl]
  rw [Fin.sum_univ_eq_sum_range (fun n => f (n + 1) - f n)]
  exact Finset.sum_range_sub f T

/-- Regret from a uniform per-step log-potential bound: if every round satisfies
`log W_{t+1} - log W_t ≤ -η · hedgeLoss_t + c`, then `regret ≤ (log N)/η + cT/η`.
This is the potential argument of [CBL06, proof of Thm 2.2] (also [FS97, §2.1, Lemma 1 and
proof of Thm 2]) with the per-round constant abstracted; both `hedge_regret_bound` (`c = η²/2`) and
`hedge_regret_bound_tight` (`c = η²/8`) are instances.

**Proof sketch.**
Step 1: sum the per-step bounds over the `T` rounds; the left side telescopes
(`log_potential_telescope`) to `log W_T - log W_0`, and the right side is
`-η · hedgeCumLoss + cT`.
Step 2: `W_0 = N` (`potential_zero`), so `log W_0 = log N`.
Step 3: `W_T ≥ exp(-η · bestExpertLoss)` (`potential_ge_best_expert`), so
`log W_T ≥ -η · bestExpertLoss`.
Step 4: combine into `-η · bestExpertLoss - log N ≤ -η · hedgeCumLoss + cT`, i.e.
`η · regret ≤ log N + cT`, and divide by `η > 0`. -/
lemma regret_le_of_log_potential_step {N T : ℕ} [NeZero N] (η : ℝ) (hη_pos : 0 < η)
    (ℓ : LossSeq N T) (c : ℝ)
    (hstep : ∀ t : Fin T, Real.log (potential η ℓ (t.val + 1)) - Real.log (potential η ℓ t.val)
      ≤ -η * hedgeLoss η ℓ t + c) :
    regret η ℓ ≤ Real.log N / η + c * T / η := by
  -- Step 1: sum the per-step bounds and telescope
  have hsum : Real.log (potential η ℓ T) - Real.log (potential η ℓ 0)
      ≤ -η * hedgeCumLoss η ℓ + c * T := by
    have hbounds := Finset.sum_le_sum fun t (_ : t ∈ Finset.univ) => hstep t
    have hrhs : ∑ t : Fin T, (-η * hedgeLoss η ℓ t + c) = -η * hedgeCumLoss η ℓ + c * T := by
      simp only [hedgeCumLoss, Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_fin]
      ring
    linarith [log_potential_telescope η ℓ]
  -- Step 2: W_0 = N
  have hW0 : Real.log (potential η ℓ 0) = Real.log N := by
    rw [potential_zero]
  -- Step 3: W_T ≥ exp(-η · bestExpertLoss)
  have hWT : Real.log (potential η ℓ T) ≥ -η * bestExpertLoss ℓ := by
    calc Real.log (potential η ℓ T) ≥ Real.log (Real.exp (-η * bestExpertLoss ℓ)) :=
          Real.log_le_log (exp_pos _) (potential_ge_best_expert η hη_pos ℓ)
      _ = -η * bestExpertLoss ℓ := Real.log_exp _
  -- Step 4: rearrange η · regret ≤ log N + cT
  unfold regret
  rw [← add_div, le_div_iff₀ hη_pos]
  nlinarith [hsum, hW0, hWT]

/-! ## Main Theorem -/

/-- **Hedge regret bound** (weak constant): for any valid loss sequence with `N` experts,
`T` rounds, and learning rate `η ∈ (0,1]`, the regret of Hedge is at most
`(ln N)/η + ηT/2` [CBL06, Thm 2.2]; [FS97, §2.1, Thm 2 / Eq. (9) (with `β = e^{-η}`)].
Deviation: the constant is `ηT/2` because the per-step bound uses the elementary chord
inequality `e^{-ηx} ≤ 1 - (1 - e^{-η})x` and the relaxation `1 - e^{-η} ≥ η - η²/2`
instead of Hoeffding's lemma.  The hypothesis `η ≤ 1` is carried over from the original
formalization; the argument does not depend on it (the relaxation holds for all `η > 0`),
so the bound is weaker than CBL's only in the constant `ηT/2` vs `ηT/8`.  CBL's constant
`ηT/8` for every `η > 0` is `hedge_regret_bound_tight`.

**Proof sketch.** The theorem instantiates the shared potential argument
`regret_le_of_log_potential_step` with `c = η²/2`.
Step 1: for each round, `log_potential_step` gives
`log W_{t+1} - log W_t ≤ -(1 - e^{-η}) · hedgeLoss_t`; relax with
`1 - e^{-η} ≥ η - η²/2` (`one_sub_exp_neg_ge`) and `hedgeLoss_t ∈ [0,1]` to get
`≤ -η · hedgeLoss_t + η²/2`.
Step 2: apply `regret_le_of_log_potential_step`.
Step 3: simplify the constant `(η²/2) · T / η = ηT/2`. -/
theorem hedge_regret_bound {N T : ℕ} [NeZero N] (η : ℝ)
    (hη_pos : 0 < η) (hη_le : η ≤ 1)
    (ℓ : LossSeq N T) (hℓ : ℓ.Valid) :
    regret η ℓ ≤ Real.log N / η + η * T / 2 := by
  -- Step 1: per-step bound `log_potential_step`, relaxed via `1 - exp(-η) ≥ η - η²/2`
  have hrelax : ∀ t : Fin T, Real.log (potential η ℓ (t.val + 1)) - Real.log (potential η ℓ t.val)
      ≤ -η * hedgeLoss η ℓ t + η ^ 2 / 2 := by
    intro t
    have h1 := log_potential_step η hη_pos ℓ hℓ t (by omega)
    have hge := @one_sub_exp_neg_ge η hη_pos
    have hle1 := hedgeLoss_le_one η ℓ hℓ t
    have hnn := hedgeLoss_nonneg η ℓ hℓ t
    nlinarith [sq_nonneg η]
  -- Step 2: shared potential argument with c = η²/2
  -- Step 3: constant algebra (η²/2)·T/η = ηT/2
  calc regret η ℓ ≤ Real.log N / η + η ^ 2 / 2 * T / η :=
        regret_le_of_log_potential_step η hη_pos ℓ (η ^ 2 / 2) hrelax
    _ = Real.log N / η + η * T / 2 := by
        congr 1
        rw [div_eq_iff (ne_of_gt hη_pos)]
        ring

/-! ## No-Regret Corollary -/

/-- The learning rate `η = √(2 ln N / T)` for `T` rounds and `N` experts [CBL06, Cor 2.2].
Deviation: CBL optimize the tight bound and take `η = √(8 ln N / T)` (that is
`optimalEtaTight`); this rate optimizes the looser `ηT/2` bound of `hedge_regret_bound`,
subject to that theorem's assumption `η ≤ 1`. -/
noncomputable def optimalEta (N T : ℕ) : ℝ :=
  Real.sqrt (2 * Real.log N / T)

/-- Balancing the two terms of a Hedge bound: for `a, T, c > 0`, at `η = √(c·a/T)` the terms
`a/η` and `η·T/c` are equal, and their sum is `√(4·a·T/c)`.  Used with `a = log N` and
`c = 2` (`hedge_regret_optimal`) or `c = 8` (`hedge_regret_tight_optimal`); this is the
optimization step of [CBL06, Cor 2.2] with the constant abstracted.

**Proof sketch.** Write `s = √(c·a/T)`, so `s > 0` and `s² = c·a/T`.
Step 1: `s² T = c a`.
Step 2: the two terms agree: `a/s = sT/c`, by cross-multiplying and Step 1.
Step 3: their sum `2sT/c` is nonnegative and squares to `4s²T²/c² = 4aT/c` (Step 1 again),
hence equals `√(4aT/c)`. -/
lemma optimalEta_balance (a T c : ℝ) (ha : 0 < a) (hT : 0 < T) (hc : 0 < c) :
    a / Real.sqrt (c * a / T) + Real.sqrt (c * a / T) * T / c = Real.sqrt (4 * a * T / c) := by
  have hs_pos : 0 < Real.sqrt (c * a / T) := Real.sqrt_pos.mpr (by positivity)
  have hs_sq : Real.sqrt (c * a / T) ^ 2 = c * a / T := Real.sq_sqrt (by positivity)
  generalize Real.sqrt (c * a / T) = s at hs_pos hs_sq ⊢
  -- Step 1: s²T = ca
  have hsT : s ^ 2 * T = c * a := by
    rw [hs_sq]
    exact div_mul_cancel₀ _ (ne_of_gt hT)
  -- Step 2: the two terms agree, a/s = sT/c
  have h1 : a / s = s * T / c := by
    rw [div_eq_div_iff (ne_of_gt hs_pos) (ne_of_gt hc)]
    linear_combination -hsT
  -- Step 3: their sum 2sT/c squares to 4aT/c
  have h2 : s * T / c + s * T / c = Real.sqrt (4 * a * T / c) := by
    rw [← Real.sqrt_sq (by positivity : 0 ≤ s * T / c + s * T / c)]
    congr 1
    rw [show s * T / c + s * T / c = 2 * s * T / c by ring, div_pow,
      div_eq_div_iff (pow_ne_zero 2 (ne_of_gt hc)) (ne_of_gt hc)]
    linear_combination (4 * T * c) * hsT
  rw [h1]
  exact h2

/-- With the learning rate `η = optimalEta N T = √(2 ln N / T)`, for `T > 0`, `N > 1` and
`T ≥ 2 ln N`, the regret of Hedge on any valid loss sequence is at most `√(2 T ln N)`
[CBL06, Cor 2.2].  Deviation: the bound is `√(2 T ln N)` rather than CBL's `√((T/2) ln N)`
because it optimizes the weak bound `hedge_regret_bound`; the hypothesis `T ≥ 2 ln N` makes
`η ≤ 1` as that bound requires.  The CBL constant is `hedge_regret_tight_optimal`.

**Proof sketch.**
Step 1: `η = √(2 ln N / T)` is positive (as `N > 1`) and, since `T ≥ 2 ln N`, at most `1`.
Step 2: apply `hedge_regret_bound` at this `η`.
Step 3: the two terms balance by `optimalEta_balance` with `a = ln N`, `c = 2`, giving
`√(4 (ln N) T / 2) = √(2 T ln N)`. -/
theorem hedge_regret_optimal {N T : ℕ} [NeZero N]
    (hT : 0 < T) (hN : 1 < N)
    (hT_large : 2 * Real.log N ≤ T)
    (ℓ : LossSeq N T) (hℓ : ℓ.Valid) :
    regret (optimalEta N T) ℓ ≤ Real.sqrt (2 * T * Real.log N) := by
  have hN_pos : (1 : ℝ) < ↑N := by exact_mod_cast hN
  have ha_pos : 0 < Real.log N := Real.log_pos hN_pos
  have hT_pos : (0 : ℝ) < ↑T := Nat.cast_pos.mpr hT
  -- Step 1: η = √(2 log N / T) is positive and, since T ≥ 2 log N, at most 1
  have hη_pos : 0 < optimalEta N T := by
    unfold optimalEta
    exact Real.sqrt_pos.mpr (div_pos (by linarith) hT_pos)
  have hη_le : optimalEta N T ≤ 1 := by
    unfold optimalEta
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by rw [div_le_one hT_pos]; linarith)
  -- Step 2: the weak bound at this η
  -- Step 3: the two terms balance (`optimalEta_balance` with c = 2)
  calc regret (optimalEta N T) ℓ
      ≤ Real.log N / optimalEta N T + optimalEta N T * T / 2 :=
        hedge_regret_bound _ hη_pos hη_le ℓ hℓ
    _ = Real.sqrt (4 * Real.log N * T / 2) :=
        optimalEta_balance (Real.log N) T 2 ha_pos hT_pos (by norm_num)
    _ = Real.sqrt (2 * T * Real.log N) := by congr 1; ring

/-- **Hedge is no-regret**: with `η = optimalEta N T`, for `T > 0`, `N > 1` and
`T ≥ 2 ln N`, the average regret `regret / T` on any valid loss sequence is at most
`√(2 ln N / T)` [CBL06, Cor 2.2].  This is a finite-`T` inequality; that the right-hand side
tends to `0` as `T → ∞` with `N` fixed (the "no-regret" property) is commentary, not part of
the formal statement.

**Proof sketch.**
Step 1: divide the cumulative bound `hedge_regret_optimal` by `T > 0`:
`regret / T ≤ √(2 T ln N) / T`.
Step 2: `√(2 T ln N) / T = √(2 ln N / T)`: both sides are nonnegative and their squares
agree, `2 T ln N / T² = 2 ln N / T`. -/
theorem hedge_no_regret {N T : ℕ} [NeZero N]
    (hT : 0 < T) (hN : 1 < N)
    (hT_large : 2 * Real.log N ≤ T)
    (ℓ : LossSeq N T) (hℓ : ℓ.Valid) :
    regret (optimalEta N T) ℓ / T ≤ Real.sqrt (2 * Real.log N / T) := by
  -- Divide the optimized cumulative regret bound by `T`.  The right side goes
  -- to zero as `T` grows with `N` fixed, which is the no-regret statement.
  have hT_pos : (0 : ℝ) < ↑T := Nat.cast_pos.mpr hT
  have hN_pos : (1 : ℝ) < ↑N := by exact_mod_cast hN
  have hlogN : 0 < Real.log ↑N := Real.log_pos hN_pos
  have hopt := hedge_regret_optimal hT hN hT_large ℓ hℓ
  -- Step 1: regret / T ≤ √(2T ln N) / T
  have h1 : regret (optimalEta N T) ℓ / ↑T ≤ Real.sqrt (2 * ↑T * Real.log N) / ↑T :=
    div_le_div_of_nonneg_right hopt hT_pos.le
  -- Step 2: √(2T ln N) / T = √(2 ln N / T)
  -- Proof: both sides are nonneg, and squaring gives 2T ln N / T² = 2 ln N / T ✓
  suffices hsuff : Real.sqrt (2 * ↑T * Real.log N) / ↑T = Real.sqrt (2 * Real.log N / ↑T) by
    linarith
  have hlhs_nn : 0 ≤ Real.sqrt (2 * ↑T * Real.log N) / ↑T :=
    div_nonneg (Real.sqrt_nonneg _) hT_pos.le
  rw [← Real.sqrt_sq hlhs_nn, ← Real.sqrt_sq (Real.sqrt_nonneg _)]
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

/-- **Hoeffding's lemma**, Bernoulli case: for `p ∈ [0,1]` and any real `h`,
`ln((1-p) + p·eʰ) ≤ p·h + h²/8`; that is, the log-moment generating function of a
`{0,1}`-valued random variable with mean `p` is at most `p·h + h²/8`
[CBL06, Lemma 2.2]; [MRT18, Lemma D.1].  Deviation: only the two-point distribution on
`{0,1}` (range length `b - a = 1`) is covered, not a general `[a,b]`-valued variable.

Specializes `bernoulli_mgf_bound` from `Hedge.Hoeffding` by substituting `η = -h`. -/
lemma hoeffding_lemma {p h : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Real.log ((1 - p) + p * Real.exp h) ≤ p * h + h ^ 2 / 8 := by
  have hb := bernoulli_mgf_bound p (-h) hp0 hp1
  simp only [neg_neg] at hb
  linarith [show -p * -h + (-h) ^ 2 / 8 = p * h + h ^ 2 / 8 from by ring]

/-- Tight one-step log-potential bound: for a valid loss sequence and `η > 0`,
`ln W_{t+1} - ln W_t ≤ -η · hedgeLoss_t + η²/8` [CBL06, proof of Thm 2.2].  The
hypothesis `ht` is only forwarded to `potential_ratio_le`, which does not use it.

**Proof sketch.** Write `μ = hedgeLoss_t ∈ [0,1]`.
Step 1: by `potential_ratio_le`, `W_{t+1}/W_t ≤ 1 - (1 - e^{-η}) μ = (1 - μ) + μ e^{-η}`.
Step 2: take logarithms (the ratio is positive).
Step 3: Hoeffding's lemma `hoeffding_lemma` with `p = μ`, `h = -η` bounds
`ln((1 - μ) + μ e^{-η}) ≤ -ημ + η²/8`. -/
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
  -- Step 1: W_{t+1}/W_t ≤ (1-μ) + μ·e^{-η} where μ = hedgeLoss
  have hratio := potential_ratio_le η hη ℓ hℓ t ht
  set μ := hedgeLoss η ℓ t
  have hμ0 := hedgeLoss_nonneg η ℓ hℓ t
  have hμ1 := hedgeLoss_le_one η ℓ hℓ t
  have hratio_pos : 0 < potential η ℓ (t.val + 1) / potential η ℓ t.val :=
    div_pos hWt1 hWt
  -- The ratio is ≤ (1-μ) + μ·e^{-η}
  have hcomp : 1 - (1 - Real.exp (-η)) * μ = (1 - μ) + μ * Real.exp (-η) := by ring
  -- Step 2: log monotonicity; Step 3: Hoeffding with p = μ, h = -η
  calc Real.log (potential η ℓ (t.val + 1) / potential η ℓ t.val)
      ≤ Real.log ((1 - μ) + μ * Real.exp (-η)) := by
        apply Real.log_le_log hratio_pos
        linarith [hcomp]
    _ ≤ μ * (-η) + (-η) ^ 2 / 8 :=
        hoeffding_lemma hμ0 hμ1
    _ = -η * μ + η ^ 2 / 8 := by ring

/-- **Hedge regret bound** (tight constant): for any valid loss sequence with `N` experts,
`T` rounds, and any learning rate `η > 0`, the regret of Hedge is at most
`(ln N)/η + ηT/8` [CBL06, Thm 2.2]; [MRT18, §8.2.4].  Deviation: stated in the expert-loss
(linear) setting rather than for a convex loss of a weighted-average prediction; the
constant and the hypotheses otherwise match CBL exactly (the prediction-space form is
`hedgePrediction_regret_bound_tight` in `Hedge.ConvexPrediction`).

This is the theorem reused by the adaptive-episode layer: once an online interaction has
generated a valid `LossSeq`, the bound applies directly.

**Proof sketch.** The theorem instantiates the shared potential argument
`regret_le_of_log_potential_step` with `c = η²/8`.
Step 1: for each round, `log_potential_step_tight` (Hoeffding's lemma) gives
`log W_{t+1} - log W_t ≤ -η · hedgeLoss_t + η²/8`; no `η ≤ 1` is needed.
Step 2: apply `regret_le_of_log_potential_step`.
Step 3: simplify the constant `(η²/8) · T / η = ηT/8`. -/
theorem hedge_regret_bound_tight {N T : ℕ} [NeZero N] (η : ℝ)
    (hη_pos : 0 < η)
    (ℓ : LossSeq N T) (hℓ : ℓ.Valid) :
    regret η ℓ ≤ Real.log N / η + η * T / 8 := by
  -- Step 1: tight per-step bound from Hoeffding's lemma (no `η ≤ 1` needed)
  have hstep : ∀ t : Fin T, Real.log (potential η ℓ (t.val + 1)) - Real.log (potential η ℓ t.val)
      ≤ -η * hedgeLoss η ℓ t + η ^ 2 / 8 :=
    fun t => log_potential_step_tight η hη_pos ℓ hℓ t (by omega)
  -- Step 2: shared potential argument with c = η²/8
  -- Step 3: constant algebra (η²/8)·T/η = ηT/8
  calc regret η ℓ ≤ Real.log N / η + η ^ 2 / 8 * T / η :=
        regret_le_of_log_potential_step η hη_pos ℓ (η ^ 2 / 8) hstep
    _ = Real.log N / η + η * T / 8 := by
        congr 1
        rw [div_eq_iff (ne_of_gt hη_pos)]
        ring

/-! ## Theorem 1 Rate with the Tight Constant -/

/-- The learning rate `η = √(8 ln N / T)` of [CBL06, Cor 2.2], which balances the two terms
`(ln N)/η` and `ηT/8` of the tight bound `hedge_regret_bound_tight`. -/
noncomputable def optimalEtaTight (N T : ℕ) : ℝ :=
  Real.sqrt (8 * Real.log N / T)

/-- With the learning rate `η = optimalEtaTight N T = √(8 ln N / T)`, for `T > 0` and
`N > 1`, the regret of Hedge on any valid loss sequence is at most `√((T/2) ln N)`
[CBL06, Cor 2.2].  This matches CBL's constant exactly; unlike `hedge_regret_optimal` no
assumption relating `T` and `ln N` is needed, since the tight bound holds for every `η > 0`.

**Proof sketch.**
Step 1: `η = √(8 ln N / T)` is positive (as `N > 1`, `T > 0`).
Step 2: apply `hedge_regret_bound_tight` at this `η`.
Step 3: the two terms balance by `optimalEta_balance` with `a = ln N`, `c = 8`, giving
`√(4 (ln N) T / 8) = √((T/2) ln N)`. -/
theorem hedge_regret_tight_optimal {N T : ℕ} [NeZero N]
    (hT : 0 < T) (hN : 1 < N)
    (ℓ : LossSeq N T) (hℓ : ℓ.Valid) :
    regret (optimalEtaTight N T) ℓ ≤ Real.sqrt (T / 2 * Real.log N) := by
  have hN_pos : (1 : ℝ) < ↑N := by exact_mod_cast hN
  have ha_pos : 0 < Real.log N := Real.log_pos hN_pos
  have hT_pos : (0 : ℝ) < ↑T := Nat.cast_pos.mpr hT
  -- Step 1: η = √(8 log N / T) is positive
  have hη_pos : 0 < optimalEtaTight N T := by
    unfold optimalEtaTight
    exact Real.sqrt_pos.mpr (div_pos (by linarith) hT_pos)
  -- Step 2: the tight bound at this η
  -- Step 3: the two terms balance (`optimalEta_balance` with c = 8)
  calc regret (optimalEtaTight N T) ℓ
      ≤ Real.log N / optimalEtaTight N T + optimalEtaTight N T * T / 8 :=
        hedge_regret_bound_tight _ hη_pos ℓ hℓ
    _ = Real.sqrt (4 * Real.log N * T / 8) :=
        optimalEta_balance (Real.log N) T 8 ha_pos hT_pos (by norm_num)
    _ = Real.sqrt (T / 2 * Real.log N) := by congr 1; ring
