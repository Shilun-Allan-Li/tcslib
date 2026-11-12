/-
Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karim Abdel Sadek, Mark Bedaywi
-/
import TCSlib.LearningTheory.Minimax.ZeroSumGame
import TCSlib.LearningTheory.Hedge.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Hedge Interaction with a Finite Zero-Sum Game

## Main definitions

- `ZeroSumGame.toLossSeq`: the loss sequence `1 − A(i, j_t)` the row player faces against a
  column-action sequence.
- `averageStrategy`, `hedgeMixedStrategy`, `empiricalStrategy`: time-averaged row strategy,
  the Hedge distribution as a mixed strategy, and the empirical column strategy.
- `prefixGameLoss`, `prefixHedgeWeight`, `prefixPotential`, `prefixHedgeMixedStrategy`,
  `hedgeResponseNat`: explicit prefix-recursive Hedge bookkeeping and the column
  best-response sequence.

## Main results

- `ZeroSumGame.toLossSeq_valid`: the induced loss sequence has losses in `[0, 1]`.
- `payoffVsPure_averageStrategy`, `pureVsPayoff_empiricalStrategy`: payoffs against the
  averaged strategies are time averages of per-round payoffs.
- `prefixGameLoss_eq_cumLoss`, `prefixHedgeWeight_eq_hedgeWeight`,
  `prefixPotential_eq_potential`, `prefixHedgeMixedStrategy_weight_eq_hedgeDist`: the
  prefix recursion agrees with `cumLoss`, `hedgeWeight`, `potential`, and `hedgeDist` of
  the induced loss sequence.
- `hedgeResponseNat_isBestResponse`: at every round the online column response is a best
  response to the Hedge distribution of the induced loss sequence.

## References

* [CBL06] N. Cesa-Bianchi, G. Lugosi, *Prediction, Learning, and Games*,
  Cambridge University Press, 2006. Chapter 7 (proof of Theorem 7.1).
* [FS99] Y. Freund, R. E. Schapire, "Adaptive game playing using multiplicative
  weights", *Games and Economic Behavior* 29(1–2):79–103, 1999. Sections 3, 5 and 6.1.

Original formalization by Karim Abdel Sadek and Mark Bedaywi.
-/

open Real Finset BigOperators

/-! ## Approximate Minimax via Hedge

The core argument: run Hedge for T rounds against the column player's
best response. The regret bound yields an approximate minimax strategy.

The row player runs Hedge on losses `1 - payoff`, so low loss means high
payoff.  The column player responds each round with a pure best response to the
current Hedge distribution.  At the end, the row strategy is the time average
of Hedge's mixed strategies, and the column strategy is the empirical
distribution of the played columns.
-/

/-- The loss sequence induced by a game and a sequence of column actions `j_t`: the loss
of row `i` at round `t` is `1 − A(i, j_t)`, so that low loss means high payoff.
[FS99, §§2–3 (there `M(i, j)` is already the row player's loss and the row player
minimizes)]; [CBL06, proof of Thm 7.1]. Deviation: payoffs/row-maximizer convention, so
the Hedge loss is `1 − A(i, j_t)`. -/
noncomputable def ZeroSumGame.toLossSeq {M N T : ℕ} (G : ZeroSumGame M N)
    (colResponse : Fin T → Fin N) : LossSeq M T :=
  fun t i => 1 - G.payoff i (colResponse t)

/-- The loss sequence induced by a game and a column-action sequence is a valid Hedge
loss sequence: every loss `1 − A(i, j_t)` lies in `[0, 1]`, because payoffs do.
[FS99, §§2–3]; [CBL06, proof of Thm 7.1]. -/
lemma ZeroSumGame.toLossSeq_valid {M N T : ℕ} (G : ZeroSumGame M N)
    (colResponse : Fin T → Fin N) : (G.toLossSeq colResponse).Valid := by
  -- Payoffs in `[0,1]` make `1 - payoff` a valid Hedge loss.
  intro t i; simp only [ZeroSumGame.toLossSeq]
  exact ⟨by linarith [G.payoff_le_one i (colResponse t)],
         by linarith [G.payoff_nonneg i (colResponse t)]⟩

/-- The time average of `T > 0` probability distributions over `n` actions, as a mixed
strategy: the weight of action `i` is `(1/T) Σ_t strategies t i`. This packages the
averaged row strategy `P̄ = (1/T) Σ_t P_t` used after running Hedge for `T` rounds.
[FS99, §5]. -/
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

/-- The Hedge distribution `hedgeDist η ℓ t` at a fixed round `t`, packaged as a mixed
strategy (with its nonnegativity and sum-one facts bundled). Currently unused elsewhere
in the library; the minimax construction uses `prefixHedgeMixedStrategy` instead. -/
noncomputable def hedgeMixedStrategy {N T : ℕ} [NeZero N]
    (η : ℝ) (ℓ : LossSeq N T) (t : ℕ) : MixedStrategy N where
  weights i := hedgeDist η ℓ t i
  nonneg i := hedgeDist_nonneg η ℓ t i
  sum_one := hedgeDist_sum η ℓ t

/-- The empirical distribution of a sequence of `T > 0` pure actions, as a mixed strategy:
the weight of action `i` is the fraction of rounds in which `i` was played. This is the
column player's final mixed strategy `Q̄` in the Hedge-vs-best-response interaction.
[FS99, §5]. -/
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

/-- The payoff of the averaged row strategy against a pure column `j` equals the time
average of the per-round payoffs `Σ_i strategies t i · A(i, j)` against that column.
[FS99, §5]. -/
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

/-- The payoff of a pure row `i` against the empirical column strategy of a sequence of
played columns equals the time average `(1/T) Σ_t A(i, j_t)` of the payoffs of `i`
against the columns actually played. [FS99, §5].

**Proof sketch.** A four-step `calc`: unfold the empirical weights and push the payoff
`A(i, x)` inside the indicator sum for each column `x`; pull the division by `T` out of
the outer sum; swap the order of summation so time is outermost; for each round `t`
collapse the indicator sum over columns `x` to the single term `x = j_t`. -/
lemma pureVsPayoff_empiricalStrategy {M N T : ℕ} [NeZero N] (G : ZeroSumGame M N)
    (hT : 0 < T) (actions : Fin T → Fin N) (i : Fin M) :
    pureVsPayoff G i (empiricalStrategy hT actions) =
      (∑ t : Fin T, G.payoff i (actions t)) / T := by
  simp only [pureVsPayoff, empiricalStrategy]
  calc ∑ x : Fin N, G.payoff i x * ((∑ t : Fin T, if actions t = x then 1 else 0) / ↑T)
      -- Step 1: push the payoff inside the indicator sum.
      = ∑ x : Fin N, (∑ t : Fin T, G.payoff i x *
            (if actions t = x then 1 else 0)) / ↑T := by
          congr 1
          ext x
          rw [← Finset.mul_sum]
          ring
      -- Step 2: pull the division by `T` out of the column sum.
    _ = (∑ x : Fin N, ∑ t : Fin T, G.payoff i x *
            (if actions t = x then 1 else 0)) / ↑T := by
          rw [Finset.sum_div]
      -- Step 3: swap the order of summation.
    _ = (∑ t : Fin T, ∑ x : Fin N, G.payoff i x *
            (if actions t = x then 1 else 0)) / ↑T := by
          rw [Finset.sum_comm]
      -- Step 4: collapse each indicator sum to the played column.
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

/-! ### Explicit Hedge Interaction -/

/-!
The next group of definitions builds the actual online play used in the
no-regret proof of approximate minimax.  The column player does not choose an
arbitrary fixed sequence in advance: at time `t`, it computes a best response to
the row player's Hedge distribution for the prefix of earlier column actions.

These prefix definitions mirror the generic Hedge definitions in
`TCSlib.LearningTheory.Hedge.Basic`, but they are written directly in terms of the already generated column actions.
The bridge lemmas below identify the prefix objects with `cumLoss`,
`hedgeWeight`, `potential`, and `hedgeDist` for the induced `LossSeq`.
-/

/-- The cumulative game loss `Σ_{s < t} (1 − A(i, j_s))` of row `i` along a finite prefix
`j_0, …, j_{t−1}` of column actions. -/
noncomputable def prefixGameLoss {M N : ℕ} (G : ZeroSumGame M N)
    {t : ℕ} (actions : Fin t → Fin N) (i : Fin M) : ℝ :=
  ∑ s : Fin t, (1 - G.payoff i (actions s))

/-- The Hedge weight `exp(−η · prefixGameLoss)` of row `i`, computed directly from a
prefix of column actions. -/
noncomputable def prefixHedgeWeight {M N : ℕ} (G : ZeroSumGame M N)
    (η : ℝ) {t : ℕ} (actions : Fin t → Fin N) (i : Fin M) : ℝ :=
  Real.exp (-η * prefixGameLoss G actions i)

/-- The prefix potential: the sum over rows of the prefix Hedge weights. -/
noncomputable def prefixPotential {M N : ℕ} (G : ZeroSumGame M N)
    (η : ℝ) {t : ℕ} (actions : Fin t → Fin N) : ℝ :=
  ∑ i : Fin M, prefixHedgeWeight G η actions i

/-- Every prefix Hedge weight is strictly positive, being an exponential. -/
lemma prefixHedgeWeight_pos {M N : ℕ} (G : ZeroSumGame M N)
    (η : ℝ) {t : ℕ} (actions : Fin t → Fin N) (i : Fin M) :
    0 < prefixHedgeWeight G η actions i :=
  Real.exp_pos _

/-- The prefix potential is strictly positive when there is at least one row, being a
nonempty sum of positive weights. -/
lemma prefixPotential_pos {M N : ℕ} [NeZero M] (G : ZeroSumGame M N)
    (η : ℝ) {t : ℕ} (actions : Fin t → Fin N) :
    0 < prefixPotential G η actions := by
  apply Finset.sum_pos
  · intro i _
    exact prefixHedgeWeight_pos G η actions i
  · exact Finset.univ_nonempty

/-- The row player's Hedge mixed strategy after seeing a prefix of column actions: row `i`
gets weight `prefixHedgeWeight i / prefixPotential`. -/
noncomputable def prefixHedgeMixedStrategy {M N : ℕ} [NeZero M] (G : ZeroSumGame M N)
    (η : ℝ) {t : ℕ} (actions : Fin t → Fin N) : MixedStrategy M where
  weights i := prefixHedgeWeight G η actions i / prefixPotential G η actions
  nonneg i := div_nonneg (prefixHedgeWeight_pos G η actions i).le
    (prefixPotential_pos G η actions).le
  sum_one := by
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt (prefixPotential_pos G η actions))

/-- The column responses generated online against Hedge: at time `t`, the history
consists of the earlier responses `s < t`; Hedge forms its mixed row strategy from that
prefix, and the column player plays a pure best response (`bestColumn`) to that mixed
strategy. Defined by well-founded recursion on `t`. [FS99, §5, Eq. (10) (the column player
plays a best response to the row's multiplicative-weights distribution)]; [CBL06, proof of
Thm 7.1]. -/
noncomputable def hedgeResponseNat {M N : ℕ} [NeZero M] [NeZero N]
    (G : ZeroSumGame M N) (η : ℝ) : ℕ → Fin N
  | t =>
      bestColumn G
        (prefixHedgeMixedStrategy G η (t := t)
          (fun s : Fin t => hedgeResponseNat G η s.val))
termination_by t => t
decreasing_by
  exact s.isLt

/-- The prefix game loss of row `i` over the first `t` actions of a sequence of `T` column
actions equals `cumLoss` at time `t` of the loss sequence induced by that sequence.

**Proof sketch.** After unfolding, both sides are sums of the loss `1 − A(i, actions s)`:
the left over all `s : Fin t`, the right over the rounds `s : Fin T` with `s < t`. Apply
`Finset.sum_bij` with the inclusion `s ↦ ⟨s, _⟩ : Fin t → Fin T`: it lands in the filtered
index set since `s < t`, it is injective (equal underlying values), every filtered index
`b < t` is the image of `⟨b, _⟩`, and the summands agree definitionally. -/
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

/-- The prefix Hedge weight of row `i` over the first `t` actions equals `hedgeWeight` at
time `t` of the induced loss sequence. -/
lemma prefixHedgeWeight_eq_hedgeWeight {M N T : ℕ} (G : ZeroSumGame M N)
    (η : ℝ) (actions : Fin T → Fin N) (t : Fin T) (i : Fin M) :
    prefixHedgeWeight G η
        (t := t.val) (fun s : Fin t.val => actions ⟨s.val, lt_trans s.isLt t.isLt⟩) i =
      hedgeWeight η (G.toLossSeq actions) t.val i := by
  simp only [prefixHedgeWeight, hedgeWeight]
  rw [prefixGameLoss_eq_cumLoss]

/-- The prefix potential over the first `t` actions equals `potential` at time `t` of the
induced loss sequence. -/
lemma prefixPotential_eq_potential {M N T : ℕ} (G : ZeroSumGame M N)
    (η : ℝ) (actions : Fin T → Fin N) (t : Fin T) :
    prefixPotential G η
        (t := t.val) (fun s : Fin t.val => actions ⟨s.val, lt_trans s.isLt t.isLt⟩) =
      potential η (G.toLossSeq actions) t.val := by
  simp only [prefixPotential, potential]
  apply Finset.sum_congr rfl
  intro i _
  exact prefixHedgeWeight_eq_hedgeWeight G η actions t i

/-- The weights of the prefix Hedge mixed strategy over the first `t` actions equal
`hedgeDist` at time `t` of the induced loss sequence. -/
lemma prefixHedgeMixedStrategy_weight_eq_hedgeDist {M N T : ℕ} [NeZero M]
    (G : ZeroSumGame M N) (η : ℝ) (actions : Fin T → Fin N) (t : Fin T) (i : Fin M) :
    (prefixHedgeMixedStrategy G η
        (t := t.val) (fun s : Fin t.val => actions ⟨s.val, lt_trans s.isLt t.isLt⟩)).weights i =
      hedgeDist η (G.toLossSeq actions) t.val i := by
  simp only [prefixHedgeMixedStrategy, hedgeDist]
  rw [prefixHedgeWeight_eq_hedgeWeight, prefixPotential_eq_potential]


/-- At each round, the online column response is a best response: against the
Hedge distribution `hedgeDist η ℓ t` (where `ℓ` is the loss sequence induced by
the responses themselves), the played column `hedgeResponseNat G η t` gives the
row player no more payoff than any fixed column `j`. [FS99, §5, Eq. (10)]; [CBL06, proof of
Thm 7.1].

**Proof sketch.** Step 1: the payoff of the prefix Hedge strategy against any column
is the `hedgeDist`-weighted payoff sum at round `t`, by
`prefixHedgeMixedStrategy_weight_eq_hedgeDist`. Step 2: by definition the played column
is `bestColumn` of the prefix Hedge strategy. Step 3: `bestColumn_spec`, rewritten
through Steps 1 and 2, is the claim. -/
lemma hedgeResponseNat_isBestResponse {M N T : ℕ} [NeZero M] [NeZero N]
    (G : ZeroSumGame M N) (η : ℝ) (t : Fin T) (j : Fin N) :
    ∑ i : Fin M, hedgeDist η (G.toLossSeq fun s : Fin T => hedgeResponseNat G η s.val) t.val i *
        G.payoff i (hedgeResponseNat G η t.val) ≤
      ∑ i : Fin M, hedgeDist η (G.toLossSeq fun s : Fin T => hedgeResponseNat G η s.val) t.val i *
        G.payoff i j := by
  let actions : Fin T → Fin N := fun s => hedgeResponseNat G η s.val
  -- Step 1: the prefix Hedge strategy's payoff against any column `j'` is the
  -- `hedgeDist`-weighted payoff sum at round `t`.
  have hpayoff : ∀ j' : Fin N,
      payoffVsPure G
          (prefixHedgeMixedStrategy G η
            (t := t.val) (fun s : Fin t.val => actions ⟨s.val, lt_trans s.isLt t.isLt⟩)) j' =
        ∑ i : Fin M, hedgeDist η (G.toLossSeq actions) t.val i * G.payoff i j' := by
    intro j'
    unfold payoffVsPure
    apply Finset.sum_congr rfl
    intro k _
    rw [prefixHedgeMixedStrategy_weight_eq_hedgeDist G η actions t k]
  -- Step 2: the played column is `bestColumn` of the prefix Hedge strategy.
  have haction :
      actions t =
        bestColumn G
          (prefixHedgeMixedStrategy G η
            (t := t.val) (fun s : Fin t.val => actions ⟨s.val, lt_trans s.isLt t.isLt⟩)) := by
    dsimp [actions]
    rw [hedgeResponseNat.eq_1]
  -- Step 3: `bestColumn_spec`, read through Steps 1 and 2.
  have hbc := bestColumn_spec G
    (prefixHedgeMixedStrategy G η
      (t := t.val) (fun s : Fin t.val => actions ⟨s.val, lt_trans s.isLt t.isLt⟩)) j
  rw [hpayoff, hpayoff, ← haction] at hbc
  exact hbc
