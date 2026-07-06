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
# Finite Two-Player Zero-Sum Games and Approximate Minimax via Hedge

## Main results

- `weak_duality`: For any mixed strategies p, q in a finite zero-sum game, min_j payoff(p,j) ≤ max_i payoff(i,q).
- `approx_minimax`: For any ε > 0 and game G with at least 2 row actions, there exist mixed strategies p, q such that payoffVsPure(G,p,j) + ε ≥ pureVsPayoff(G,i,q) for all pure i,j.
- `minimax_approx_theorem`: For every ε > 0 there exist mixed strategies achieving an ε-approximate saddle point.

## References

- Original formalization by Karim Abdel Sadek and Mark Bedaywi
-/

/-! ## Game Setup -/

/-- A finite two-player zero-sum game with payoffs in [0,1]. -/
-- `M` is the number of row actions and `N` is the number of column actions.
-- The row player wants larger payoffs; the column player wants smaller payoffs.
structure ZeroSumGame (M N : ℕ) where
  payoff : Fin M → Fin N → ℝ
  payoff_nonneg : ∀ i j, 0 ≤ payoff i j
  payoff_le_one : ∀ i j, payoff i j ≤ 1

/-- A mixed strategy: a probability distribution over Fin n. -/
-- We keep mixed strategies as explicit weights plus probability laws.  This is
-- enough for finite games and avoids extra simplex infrastructure.
structure MixedStrategy (n : ℕ) where
  weights : Fin n → ℝ
  nonneg : ∀ i, 0 ≤ weights i
  sum_one : ∑ i : Fin n, weights i = 1

/-- Expected payoff to the row player against a pure column j. -/
-- This is `pᵀ A e_j`: row mixes, column is pure.
noncomputable def payoffVsPure {M N : ℕ} (G : ZeroSumGame M N)
    (p : MixedStrategy M) (j : Fin N) : ℝ :=
  ∑ i : Fin M, p.weights i * G.payoff i j

/-- Expected payoff when row plays pure i against mixed column q. -/
-- This is `e_iᵀ A q`: row is pure, column mixes.
noncomputable def pureVsPayoff {M N : ℕ} (G : ZeroSumGame M N)
    (i : Fin M) (q : MixedStrategy N) : ℝ :=
  ∑ j : Fin N, G.payoff i j * q.weights j

/-- A pure column best response minimizing payoff against a row mixed strategy. -/
-- Finiteness lets us choose an actual minimizer, not just an infimum.
noncomputable def bestColumn {M N : ℕ} [NeZero N] (G : ZeroSumGame M N)
    (p : MixedStrategy M) : Fin N :=
  Classical.choose (Finite.exists_min (payoffVsPure G p))

-- The chosen column does no worse for the column player than any other column.
lemma bestColumn_spec {M N : ℕ} [NeZero N] (G : ZeroSumGame M N)
    (p : MixedStrategy M) (j : Fin N) :
    payoffVsPure G p (bestColumn G p) ≤ payoffVsPure G p j := by
  exact (Classical.choose_spec (Finite.exists_min (payoffVsPure G p))) j

/-- A pure row best response maximizing payoff against a column mixed strategy. -/
-- This is the row-player analogue of `bestColumn`.
noncomputable def bestRow {M N : ℕ} [NeZero M] (G : ZeroSumGame M N)
    (q : MixedStrategy N) : Fin M :=
  Classical.choose (Finite.exists_max (fun i : Fin M => pureVsPayoff G i q))

-- The chosen row gets at least as much payoff as any other row.
lemma bestRow_spec {M N : ℕ} [NeZero M] (G : ZeroSumGame M N)
    (q : MixedStrategy N) (i : Fin M) :
    pureVsPayoff G i q ≤ pureVsPayoff G (bestRow G q) q := by
  exact (Classical.choose_spec (Finite.exists_max (fun i : Fin M => pureVsPayoff G i q))) i

/-! ## Weak Duality -/

/-- For any strategies p, q: min_j payoff(p,j) ≤ max_i payoff(i,q). -/
theorem weak_duality {M N : ℕ} [NeZero M] [NeZero N] (G : ZeroSumGame M N)
    (p : MixedStrategy M) (q : MixedStrategy N) :
    (⨅ j : Fin N, payoffVsPure G p j) ≤ ⨆ i : Fin M, pureVsPayoff G i q := by
  -- Put the bilinear expected payoff in the middle.  It is at least the worst
  -- pure-column payoff against `p`, and at most the best pure-row payoff
  -- against `q`.
  set v := ∑ i : Fin M, ∑ j : Fin N, p.weights i * G.payoff i j * q.weights j
  have hv_lb : ⨅ j, payoffVsPure G p j ≤ v := by
    -- Rewrite `v` as an average over columns and compare each term to the
    -- column infimum.
    have hv_eq : v = ∑ j : Fin N, payoffVsPure G p j * q.weights j := by
      simp only [v, payoffVsPure]; rw [Finset.sum_comm]; simp_rw [Finset.sum_mul]
    rw [hv_eq]
    have hbdd : BddBelow (Set.range (payoffVsPure G p)) :=
      ⟨0, by rintro _ ⟨j, rfl⟩; exact Finset.sum_nonneg fun i _ =>
        mul_nonneg (p.nonneg i) (G.payoff_nonneg i j)⟩
    calc ⨅ j, payoffVsPure G p j
        = (⨅ j, payoffVsPure G p j) * ∑ j, q.weights j := by rw [q.sum_one, mul_one]
      _ = ∑ j, (⨅ j, payoffVsPure G p j) * q.weights j := Finset.mul_sum ..
      _ ≤ ∑ j, payoffVsPure G p j * q.weights j :=
          Finset.sum_le_sum fun j _ =>
            mul_le_mul_of_nonneg_right (ciInf_le hbdd j) (q.nonneg j)
  have hv_ub : v ≤ ⨆ i, pureVsPayoff G i q := by
    -- Rewrite `v` as an average over rows and compare each term to the row
    -- supremum.
    have hv_eq : v = ∑ i : Fin M, pureVsPayoff G i q * p.weights i := by
      simp only [v, pureVsPayoff]; simp_rw [Finset.sum_mul]
      congr 1; ext i; congr 1; ext j; ring
    rw [hv_eq]
    have hbdd : BddAbove (Set.range (pureVsPayoff G · q)) :=
      ⟨1, by rintro _ ⟨i, rfl⟩
             calc ∑ j : Fin N, G.payoff i j * q.weights j
                 ≤ ∑ j : Fin N, 1 * q.weights j :=
                   Finset.sum_le_sum fun j _ =>
                     mul_le_mul_of_nonneg_right (G.payoff_le_one i j) (q.nonneg j)
               _ = 1 := by simp [q.sum_one]⟩
    calc ∑ i, pureVsPayoff G i q * p.weights i
        ≤ ∑ i, (⨆ i, pureVsPayoff G i q) * p.weights i :=
          Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_right (le_ciSup hbdd i) (p.nonneg i)
      _ = (⨆ i, pureVsPayoff G i q) := by
          rw [← Finset.mul_sum]; rw [p.sum_one, mul_one]
  linarith

/-! ## Approximate Minimax via Hedge

The core argument: run Hedge for T rounds against the column player's
best response. The regret bound yields an approximate minimax strategy.

The row player runs Hedge on losses `1 - payoff`, so low loss means high
payoff.  The column player responds each round with a pure best response to the
current Hedge distribution.  At the end, the row strategy is the time average
of Hedge's mixed strategies, and the column strategy is the empirical
distribution of the played columns.
-/

/-- A game induces a valid loss sequence for any column response sequence.
    Loss for row i at round t is 1 - A(i, j_t) ∈ [0,1]. -/
noncomputable def ZeroSumGame.toLossSeq {M N T : ℕ} (G : ZeroSumGame M N)
    (colResponse : Fin T → Fin N) : LossSeq M T :=
  fun t i => 1 - G.payoff i (colResponse t)

lemma ZeroSumGame.toLossSeq_valid {M N T : ℕ} (G : ZeroSumGame M N)
    (colResponse : Fin T → Fin N) : (G.toLossSeq colResponse).Valid := by
  -- Payoffs in `[0,1]` make `1 - payoff` a valid Hedge loss.
  intro t i; simp only [ZeroSumGame.toLossSeq]
  exact ⟨by linarith [G.payoff_le_one i (colResponse t)],
         by linarith [G.payoff_nonneg i (colResponse t)]⟩

/-- The average of T distributions is a distribution. -/
-- This packages the average row strategy used after running Hedge for `T`
-- rounds.
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

/-- The Hedge distribution at a fixed round, packaged as a mixed strategy. -/
-- This is just `hedgeDist` with its nonnegativity and sum-one facts bundled.
noncomputable def hedgeMixedStrategy {N T : ℕ} [NeZero N]
    (η : ℝ) (ℓ : LossSeq N T) (t : ℕ) : MixedStrategy N where
  weights i := hedgeDist η ℓ t i
  nonneg i := hedgeDist_nonneg η ℓ t i
  sum_one := hedgeDist_sum η ℓ t

/-- The empirical distribution of a sequence of pure strategies. -/
-- The column player's final mixed strategy counts how often each pure column
-- was played.
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

-- Payoff against a pure column under the averaged row strategy equals the
-- average of the per-round payoffs against that column.
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

-- Payoff of a pure row against the empirical column strategy equals the average
-- payoff of that row against the columns actually played.
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

/-! ### Explicit Hedge Interaction -/

/-!
The next group of definitions builds the actual online play used in the
no-regret proof of approximate minimax.  The column player does not choose an
arbitrary fixed sequence in advance: at time `t`, it computes a best response to
the row player's Hedge distribution for the prefix of earlier column actions.

These prefix definitions mirror the generic Hedge definitions in `Hedge.lean`,
but they are written directly in terms of the already generated column actions.
The bridge lemmas below identify the prefix objects with `cumLoss`,
`hedgeWeight`, `potential`, and `hedgeDist` for the induced `LossSeq`.
-/

-- Cumulative game loss of row `i` along a finite prefix of column actions.
noncomputable def prefixGameLoss {M N : ℕ} (G : ZeroSumGame M N)
    {t : ℕ} (actions : Fin t → Fin N) (i : Fin M) : ℝ :=
  ∑ s : Fin t, (1 - G.payoff i (actions s))

-- The Hedge weight computed directly from a prefix of column actions.
noncomputable def prefixHedgeWeight {M N : ℕ} (G : ZeroSumGame M N)
    (η : ℝ) {t : ℕ} (actions : Fin t → Fin N) (i : Fin M) : ℝ :=
  Real.exp (-η * prefixGameLoss G actions i)

-- The corresponding prefix potential.
noncomputable def prefixPotential {M N : ℕ} (G : ZeroSumGame M N)
    (η : ℝ) {t : ℕ} (actions : Fin t → Fin N) : ℝ :=
  ∑ i : Fin M, prefixHedgeWeight G η actions i

-- Prefix weights are positive because they are exponentials.
lemma prefixHedgeWeight_pos {M N : ℕ} (G : ZeroSumGame M N)
    (η : ℝ) {t : ℕ} (actions : Fin t → Fin N) (i : Fin M) :
    0 < prefixHedgeWeight G η actions i :=
  Real.exp_pos _

-- Therefore the prefix potential is positive.
lemma prefixPotential_pos {M N : ℕ} [NeZero M] (G : ZeroSumGame M N)
    (η : ℝ) {t : ℕ} (actions : Fin t → Fin N) :
    0 < prefixPotential G η actions := by
  apply Finset.sum_pos
  · intro i _
    exact prefixHedgeWeight_pos G η actions i
  · exact Finset.univ_nonempty

-- The row player's mixed strategy after seeing a prefix of column actions.
noncomputable def prefixHedgeMixedStrategy {M N : ℕ} [NeZero M] (G : ZeroSumGame M N)
    (η : ℝ) {t : ℕ} (actions : Fin t → Fin N) : MixedStrategy M where
  weights i := prefixHedgeWeight G η actions i / prefixPotential G η actions
  nonneg i := div_nonneg (prefixHedgeWeight_pos G η actions i).le
    (prefixPotential_pos G η actions).le
  sum_one := by
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt (prefixPotential_pos G η actions))

/-- Column responses generated online against Hedge.

At time `t`, the history consists of the earlier responses `s : Fin t`.  Hedge
forms its mixed row strategy from that prefix, and the column player chooses a
pure best response to that mixed strategy. -/
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

/-- **Regret-to-Game Bridge** (Cesa-Bianchi & Lugosi, Ch. 7):
    If row player achieves regret ≤ R against column best responses,
    then the average row strategy is approximately minimax optimal.

    Specifically: for T rounds with regret R, for the average strategy p̄
    and any mixed column strategy q:
      ⨅ j, payoffVsPure(G, p̄, j) ≥ ⨆ i, pureVsPayoff(G, i, q̂) - R/T
    where q̂ is the empirical distribution of column responses. -/
-- Step 1: The regret bound translated to payoffs.
-- If ∑_t ⟨p_t, 1 - A(·, j_t)⟩ - min_i ∑_t (1 - A(i, j_t)) ≤ R,
-- then ∑_t payoffVsPure(p_t, j_t) ≥ max_i ∑_t A(i, j_t) - R.
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

-- Step 2: Average of min ≤ min of average (for linear functions).
-- (1/T) ∑_t min_j f(p_t, j) ≤ min_j (1/T) ∑_t f(p_t, j) = min_j f(p̄, j)
-- This holds because for any fixed j:
-- (1/T) ∑_t min_j' f(p_t, j') ≤ (1/T) ∑_t f(p_t, j)
-- Taking min over j of the RHS gives the result.
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

/-- **Hedge construction lemma**:
    Given a game G with M ≥ 2 rows, T rounds, and η > 0,
    there exist mixed strategies p, q such that for all i, j:
      payoffVsPure(G, p, j) + (log M)/η/T + η/8 ≥ pureVsPayoff(G, i, q).

    The construction:
    1. Run Hedge for T rounds where column plays best response at each step
    2. p = average of Hedge distributions, q = empirical column distribution
    3. The regret bound gives the gap ≤ (log M)/η + ηT/8, divided by T.

    This requires building the explicit Hedge interaction (argmin for column
    best responses, converting hedgeDist to MixedStrategy, etc.) which is
    very involved in Lean. -/
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

theorem approx_minimax {M N : ℕ} [NeZero M] [NeZero N] (G : ZeroSumGame M N)
    (hM : 1 < M) (ε : ℝ) (hε : 0 < ε) :
    ∃ (p : MixedStrategy M) (q : MixedStrategy N),
      ∀ (i : Fin M) (j : Fin N),
        payoffVsPure G p j + ε ≥ pureVsPayoff G i q := by
  -- Choose `η` and `T` so the explicit error
  -- `(log M / η + ηT / 8) / T` from `hedge_construction` is at most `ε`.
  -- We need to choose T and η so that (log M)/η/T + η/8 ≤ ε.
  -- With the tight bound, regret/T ≤ (log M)/(ηT) + η/8.
  -- Setting η = √(8 log M / T), this becomes √(8 log M / T) / 4 + √(8 log M / T) / 8
  --   = (3/8)√(8 log M / T) which → 0 as T → ∞.
  -- We just need to find T large enough.
  -- Simpler: set η = min(1, ε/2) and T = ⌈2 log M / (η * ε)⌉ + 1.
  -- Then (log M)/(ηT) ≤ ε/2 and ηT/8/T = η/8 ≤ ε/16 < ε/2.
  -- So the total bound is < ε.
  --
  -- Choose explicit parameters so that the regret bound divided by T is at most ε.
  have hM_pos : (1 : ℝ) < ↑M := by exact_mod_cast hM
  have hlogM_pos : 0 < Real.log (↑M) := Real.log_pos hM_pos
  -- Choose η = min 1 (4 * ε / 5)
  set η := min 1 (4 * ε / 5)
  have hη_pos : 0 < η := lt_min one_pos (by linarith)
  have hη_le_ε : η ≤ 4 * ε / 5 := min_le_right _ _
  -- Choose T large enough that (log M)/(η * T) ≤ ε/2
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
  obtain ⟨p, q, hpq⟩ := hedge_construction G hM T hT_pos η hη_pos
  exact ⟨p, q, fun i j => by
    have hbound := hpq i j
    -- Show: (log M / η + η * T / 8) / T ≤ ε
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

**Proved:** weak_duality, regret_to_payoff, avg_min_le_min_avg, hedge_construction,
  and approx_minimax.

The exact finite minimax theorem requires one additional compactness/attainment
layer for finite simplices. The no-regret part gives the standard arbitrarily
good approximate saddle point, stated below.
-/

theorem minimax_approx_theorem {M N : ℕ} [NeZero M] [NeZero N]
    (G : ZeroSumGame M N) (hM : 1 < M) :
    ∀ ε : ℝ, 0 < ε →
      ∃ (p : MixedStrategy M) (q : MixedStrategy N),
        ∀ (i : Fin M) (j : Fin N),
          payoffVsPure G p j + ε ≥ pureVsPayoff G i q := by
  intro ε hε
  exact approx_minimax G hM ε hε
