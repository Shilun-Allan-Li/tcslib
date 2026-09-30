/-
Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karim Abdel Sadek, Mark Bedaywi
-/
import TCSlib.LearningTheory.Minimax.HedgeInteraction
import TCSlib.LearningTheory.Hedge.Regret

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Approximate Minimax via Hedge

## Main definitions

None (this file only proves theorems about `ZeroSumGame` and `MixedStrategy`).

## Main results

- `regret_to_payoff`: the regret-to-game bridge — a loss-regret bound `R` for the row
  player's distributions against a column sequence is a payoff guarantee: the realized
  payoff sum is at least the best fixed row's payoff sum minus `R`.
- `avg_min_le_min_avg`: the average of minima is at most the minimum of the average
  (currently unused).
- `approx_minimax`: for any `ε > 0` and game `G` with at least 2 row actions, there exist
  mixed strategies `p`, `q` such that `payoffVsPure G p j + ε ≥ pureVsPayoff G i q` for all
  pure `i`, `j` — an ε-approximate saddle point, built by running Hedge against column
  best responses.
- `minimax_approx_theorem`: `approx_minimax` with `ε` universally quantified.

## References

* [CBL06] N. Cesa-Bianchi, G. Lugosi, *Prediction, Learning, and Games*,
  Cambridge University Press, 2006. Chapter 7 (Theorem 7.1 and its proof).
* [FS99] Y. Freund, R. E. Schapire, "Adaptive game playing using multiplicative
  weights", *Games and Economic Behavior* 29(1–2):79–103, 1999. Sections 5–6.1.

Original formalization by Karim Abdel Sadek and Mark Bedaywi.
-/

open Real Finset BigOperators

/-- The regret-to-payoff bridge: for `T` rounds in which the row player plays the
distributions `p_t` (each summing to one) and the column player plays `j_t`, if the row
player's loss regret on the losses `1 − A(i, j_t)` is at most `R`, i.e.
`Σ_t Σ_i p_t(i) · (1 − A(i, j_t)) − inf_i Σ_t (1 − A(i, j_t)) ≤ R`, then the realized
payoff sum satisfies `Σ_t Σ_i p_t(i) · A(i, j_t) ≥ sup_i Σ_t A(i, j_t) − R`.
[CBL06, proof of Thm 7.1]; [FS99, §5].

Regret is stated for losses, but the game is stated in payoffs; since loss is
`1 − payoff`, the learner's loss regret becomes a payoff guarantee against the best fixed
row action in hindsight.

**Proof sketch.** Step 1: since each `p_t` sums to one, the loss sum equals `T` minus the
payoff sum. Step 2: the infimum over rows of `Σ_t (1 − A(i, j_t)) = T − Σ_t A(i, j_t)`
equals `T` minus the supremum of the payoff sums (both directions of `le_antisymm`, using
that the ranges are finite, hence bounded). Step 3: substituting Steps 1–2 into the
hypothesis gives `sup_i Σ_t A(i, j_t) − Σ_t Σ_i p_t(i) A(i, j_t) ≤ R`. Step 4: the goal's
supremum of `Σ_t A(i, j_t) − R` equals the supremum of the payoff sums minus `R` (the
constant `R` does not depend on `i`); the claim then follows by linear arithmetic. -/
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
  -- Step 1: the loss sum is `T` minus the payoff sum.
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
  -- Step 2: the infimum of `T − f` is `T` minus the supremum of `f`.
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
  -- Step 3: substitute into the hypothesis.
  -- Now the hypothesis becomes (T - S_pay) - (T - S_max) ≤ R, so S_max - S_pay ≤ R
  rw [hlhs, hrhs] at hregret
  -- Step 4: pull the constant `R` out of the goal's supremum and conclude.
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

/-- The average of minima is at most the minimum of the average: for `T > 0` and any
`f : Fin T → Fin N → ℝ`, `(1/T) Σ_t inf_j f t j ≤ inf_j (1/T) Σ_t f t j`. This holds
because for any fixed `j`, every per-round minimum is at most `f t j`; sum, divide, and
take the infimum over `j`. Currently unused elsewhere in the library (the minimax
construction goes through `regret_to_payoff` instead). -/
lemma avg_min_le_min_avg {N T : ℕ} [NeZero N] (hT : 0 < T)
    (f : Fin T → Fin N → ℝ) :
    (1 / T : ℝ) * ∑ t : Fin T, ⨅ j : Fin N, f t j ≤
    ⨅ j : Fin N, (1 / T : ℝ) * ∑ t : Fin T, f t j := by
  -- For each fixed `j₀`, every per-round minimum is at most `f t j₀`.
  -- Sum and divide, then take the infimum over `j₀`.
  apply le_ciInf
  intro j₀
  have hbdd : ∀ t, BddBelow (Set.range (f t)) :=
    fun t => Set.Finite.bddBelow (Set.finite_range _)
  apply mul_le_mul_of_nonneg_left _ (le_of_lt (div_pos one_pos (Nat.cast_pos.mpr hT)))
  exact Finset.sum_le_sum fun t _ => ciInf_le (hbdd t) j₀

/-- The Hedge construction: given a game `G` with `M ≥ 2` rows, a horizon `T > 0`, and a
learning rate `η > 0`, there exist mixed strategies `p`, `q` such that for all pure `i`,
`j`, `payoffVsPure G p j + (log M / η + η T / 8) / T ≥ pureVsPayoff G i q`. Here `p` is
the time average of the Hedge distributions played on the losses `1 − A(·, j_t)` and `q`
is the empirical distribution of the columns `j_t`, each of which is a pure best response
to the current Hedge distribution. [FS99, §§5–6.1]; [CBL06, proof of Thm 7.1]. The hypothesis
`1 < M` is not used by this lemma's proof (it is carried for `approx_minimax`).

**Proof sketch.** Step 1 (`hvalid`): generate the online column responses
`hedgeResponseNat`, form the induced loss sequence `ℓ` (valid, since payoffs lie in
`[0, 1]`), and record the Hedge distributions `strategies t := hedgeDist η ℓ t`; take
`p := averageStrategy` and `q := empiricalStrategy`. Step 2 (`hreg`): the tight Hedge
regret bound `log M / η + η T / 8` on `ℓ` (`hedge_regret_bound_tight`), read through
`regret_to_payoff`, says the realized payoff sum is at least the best fixed row's payoff
sum minus `R`. Step 3 (`hbest_sum`): by `hedgeResponseNat_isBestResponse`, replacing each
played column by the fixed column `j` can only increase the row payoff, round by round.
Step 4 (`hmain`): for the fixed row `i`, chain Steps 2 and 3 (`i`'s payoff sum is at most
the supremum) and divide by `T`. Step 5 (`hpj`, `hqi`): both sides of the goal are the
time averages computed in `payoffVsPure_averageStrategy` and
`pureVsPayoff_empiricalStrategy`; conclude by linear arithmetic. -/
private lemma hedge_construction {M N : ℕ} [NeZero M] [NeZero N] (G : ZeroSumGame M N)
    (_hM : 1 < M)
    (T : ℕ) (hT : 0 < T)
    (η : ℝ) (hη_pos : 0 < η) :
    ∃ (p : MixedStrategy M) (q : MixedStrategy N),
      ∀ (i : Fin M) (j : Fin N),
        payoffVsPure G p j + (Real.log M / η + η * T / 8) / T ≥
          pureVsPayoff G i q := by
  classical
  -- Step 1 (`hvalid`): generate the online column responses, turn them into a
  -- valid Hedge loss sequence, and record the row distributions Hedge plays.
  let actions : Fin T → Fin N := fun t => hedgeResponseNat G η t.val
  let ℓ : LossSeq M T := G.toLossSeq actions
  let strategies : Fin T → Fin M → ℝ := fun t i => hedgeDist η ℓ t.val i
  have h_nonneg : ∀ t i, 0 ≤ strategies t i := fun t i => hedgeDist_nonneg η ℓ t.val i
  have h_sum : ∀ t, ∑ i : Fin M, strategies t i = 1 := fun t => hedgeDist_sum η ℓ t.val
  have hvalid : ℓ.Valid := ZeroSumGame.toLossSeq_valid G actions
  refine ⟨averageStrategy hT strategies h_nonneg h_sum, empiricalStrategy hT actions, ?_⟩
  intro i j
  set R : ℝ := Real.log ↑M / η + η * ↑T / 8 with hR
  -- Step 2 (`hreg`): the tight Hedge bound on `ℓ`, translated into a payoff
  -- guarantee against the best fixed row action (`regret_to_payoff`).
  have hreg :
      ∑ t : Fin T, ∑ i : Fin M, strategies t i * G.payoff i (actions t) ≥
        ⨆ i : Fin M, ∑ t : Fin T, G.payoff i (actions t) - R := by
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
      simpa only [R, regret, hedgeCumLoss, hedgeLoss, strategies, ℓ, ZeroSumGame.toLossSeq,
        hbestEq] using hedge_regret_bound_tight η hη_pos ℓ hvalid
    exact regret_to_payoff G hT strategies h_sum actions R hreg'
  -- Step 3 (`hbest_sum`): each generated column is a best response to the
  -- current Hedge distribution, so replacing it by the fixed column `j` can
  -- only increase the row payoff, round by round.
  have hbest_sum :
      ∑ t : Fin T, ∑ i : Fin M, strategies t i * G.payoff i (actions t) ≤
        ∑ t : Fin T, ∑ i : Fin M, strategies t i * G.payoff i j :=
    Finset.sum_le_sum fun t _ => hedgeResponseNat_isBestResponse G η t j
  -- Step 4 (`hmain`): combine Steps 2 and 3 for the fixed row `i`, then divide
  -- by `T`.
  have hmain :
      (∑ t : Fin T, G.payoff i (actions t)) / ↑T - R / ↑T ≤
        (∑ t : Fin T, ∑ i : Fin M, strategies t i * G.payoff i j) / ↑T := by
    have hi_sup : (∑ t : Fin T, G.payoff i (actions t)) - R ≤
        ⨆ i : Fin M, ∑ t : Fin T, G.payoff i (actions t) - R := by
      have hbdd : BddAbove (Set.range (fun i : Fin M => ∑ t : Fin T, G.payoff i (actions t) - R)) :=
        Set.Finite.bddAbove (Set.finite_range _)
      exact le_ciSup hbdd i
    have hTpos : (0 : ℝ) < ↑T := Nat.cast_pos.mpr hT
    have := div_le_div_of_nonneg_right (show ∑ t : Fin T, G.payoff i (actions t) - R ≤
        ∑ t : Fin T, ∑ i : Fin M, strategies t i * G.payoff i j by linarith) hTpos.le
    field_simp at this ⊢
    linarith
  -- Step 5 (`hpj`, `hqi`): both sides of the goal are time averages.
  have hpj :
      payoffVsPure G (averageStrategy hT strategies h_nonneg h_sum) j =
        (∑ t : Fin T, ∑ i : Fin M, strategies t i * G.payoff i j) / ↑T :=
    payoffVsPure_averageStrategy G hT strategies h_nonneg h_sum j
  have hqi :
      pureVsPayoff G i (empiricalStrategy hT actions) =
        (∑ t : Fin T, G.payoff i (actions t)) / ↑T :=
    pureVsPayoff_empiricalStrategy G hT actions i
  rw [hpj, hqi, hR]
  linarith

/-- The approximate minimax theorem for finite zero-sum games: for any game `G` with at
least two row actions and any `ε > 0`, there exist a row mixed strategy `p` and a column
mixed strategy `q` forming an ε-approximate saddle point, i.e.
`payoffVsPure G p j + ε ≥ pureVsPayoff G i q` for all pure rows `i` and columns `j`.
[CBL06, Thm 7.1 (finite case, i.e. von Neumann's minimax theorem)]; [FS99, §5 (proof of
the minmax theorem), §6.1 (approximate minimax via multiplicative weights)]. Deviation: the
sources state the exact minimax equality (or an `O(√(log M / T))` rate); here the
conclusion is an ε-approximate
saddle point with the explicit parameter choice `η = min 1 (4ε/5)` and
`T = ⌈2 log M / (η ε)⌉ + 1`, and the hypothesis `1 < M` (Hedge needs at least two
experts; it makes `log M > 0`) is carried from the Hedge bound. The exact finite value is
derived in `Minimax.ConvexMinimaxCore.finite_minimax_value`.

**Proof sketch.** Step 1: choose the learning rate `η := min 1 (4ε/5)`, so `0 < η ≤ 4ε/5`.
Step 2: choose the horizon `T := ⌈2 log M / (η ε)⌉ + 1`, so that `T > 0` and
`log M / (η T) ≤ ε/2`. Step 3: apply `hedge_construction` with these parameters to get
`p`, `q` with error `(log M / η + η T / 8) / T`. Step 4: this error splits as
`log M / (η T) + η / 8 ≤ ε/2 + ε/10 ≤ ε`, which gives the claim. -/
theorem approx_minimax {M N : ℕ} [NeZero M] [NeZero N] (G : ZeroSumGame M N)
    (hM : 1 < M) (ε : ℝ) (hε : 0 < ε) :
    ∃ (p : MixedStrategy M) (q : MixedStrategy N),
      ∀ (i : Fin M) (j : Fin N),
        payoffVsPure G p j + ε ≥ pureVsPayoff G i q := by
  -- Choose `η` and `T` so the explicit error
  -- `(log M / η + ηT / 8) / T` from `hedge_construction` is at most `ε`.
  -- With the tight bound, regret/T ≤ (log M)/(ηT) + η/8.
  have hM_pos : (1 : ℝ) < ↑M := by exact_mod_cast hM
  have hlogM_pos : 0 < Real.log (↑M) := Real.log_pos hM_pos
  -- Step 1: choose η = min 1 (4 * ε / 5)
  set η := min 1 (4 * ε / 5)
  have hη_pos : 0 < η := lt_min one_pos (by linarith)
  have hη_le_ε : η ≤ 4 * ε / 5 := min_le_right _ _
  -- Step 2: choose T large enough that (log M)/(η * T) ≤ ε/2
  -- i.e., T ≥ 2 * log M / (η * ε)
  obtain ⟨T, hT_pos, hT_large⟩ : ∃ T : ℕ, 0 < T ∧
      Real.log ↑M / (η * ↑T) ≤ ε / 2 := by
    -- T = ⌈2 * log M / (η * ε)⌉ + 1 works
    refine ⟨⌈2 * Real.log ↑M / (η * ε)⌉₊ + 1, Nat.succ_pos _, ?_⟩
    have hηT_pos : 0 < η * ↑(⌈2 * Real.log ↑M / (η * ε)⌉₊ + 1) :=
      mul_pos hη_pos (by exact_mod_cast Nat.succ_pos _)
    rw [div_le_iff₀ hηT_pos]
    set T' := ⌈2 * Real.log ↑M / (η * ε)⌉₊ + 1
    have hT'_ge : (T' : ℝ) ≥ 2 * Real.log ↑M / (η * ε) := by
      have : (⌈2 * Real.log ↑M / (η * ε)⌉₊ : ℝ) ≥ 2 * Real.log ↑M / (η * ε) :=
        Nat.le_ceil _
      simp only [T', Nat.cast_add, Nat.cast_one]
      linarith
    calc Real.log ↑M
        = ε / 2 * (η * (2 * Real.log ↑M / (η * ε))) := by field_simp
      _ ≤ ε / 2 * (η * ↑T') := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          exact mul_le_mul_of_nonneg_left hT'_ge.le (le_of_lt hη_pos)
  -- Step 3: run the Hedge construction with these parameters.
  obtain ⟨p, q, hpq⟩ := hedge_construction G hM T hT_pos η hη_pos
  exact ⟨p, q, fun i j => by
    have hbound := hpq i j
    -- Step 4: show the error is at most ε: (log M / η + η * T / 8) / T ≤ ε
    suffices hle : (Real.log ↑M / η + η * ↑T / 8) / ↑T ≤ ε by linarith
    have hT_pos_r : (0 : ℝ) < ↑T := Nat.cast_pos.mpr hT_pos
    rw [add_div, div_div]
    -- First term: log M / (η * T) ≤ ε/2
    -- Second term: η * T / 8 / T = η / 8 ≤ (4ε/5) / 8 = ε/10
    have h1 := hT_large
    have h2 : η * ↑T / 8 / ↑T = η / 8 := by
      field_simp
    rw [h2]
    have h3 : η / 8 ≤ ε / 2 := by
      calc η / 8 ≤ (4 * ε / 5) / 8 := by linarith [hη_le_ε]
        _ = ε / 10 := by ring
        _ ≤ ε / 2 := by linarith
    linarith⟩

/-! ## Summary

The no-regret argument (`approx_minimax`) gives an arbitrarily good approximate saddle
point; the exact finite value is derived in `Minimax.ConvexMinimaxCore`. -/

/-- The ε-approximate minimax theorem, quantified over all `ε`: for any game `G` with at
least two row actions and every `ε > 0`, there exist mixed strategies `p`, `q` with
`payoffVsPure G p j + ε ≥ pureVsPayoff G i q` for all pure `i`, `j`. This is
`approx_minimax` with `ε` universally quantified. [CBL06, Thm 7.1 (finite case)];
[FS99, §5]. -/
theorem minimax_approx_theorem {M N : ℕ} [NeZero M] [NeZero N]
    (G : ZeroSumGame M N) (hM : 1 < M) :
    ∀ ε : ℝ, 0 < ε →
      ∃ (p : MixedStrategy M) (q : MixedStrategy N),
        ∀ (i : Fin M) (j : Fin N),
          payoffVsPure G p j + ε ≥ pureVsPayoff G i q := by
  intro ε hε
  exact approx_minimax G hM ε hε
