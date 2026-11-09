/-
Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karim Abdel Sadek, Mark Bedaywi
-/
import TCSlib.LearningTheory.Minimax.FiniteMinimax

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Coarse Correlated Equilibria

## Main definitions

- `Game`, `ZeroSumGame.toGame`: finite two-player games with separate utilities, and the
  embedding of a zero-sum game.
- `JointDistribution`: a probability distribution over action profiles, with its marginals
  (`rowMarginal`, `colMarginal`), expected utilities (`rowExpectedUtility`,
  `colExpectedUtility`) and unilateral-deviation utilities (`rowDeviationUtility`,
  `colDeviationUtility`).
- `IsCoarseCorrelatedEquilibrium`, `IsApproxCoarseCorrelatedEquilibrium`: exact and
  `ε`-approximate coarse correlated equilibria.
- `productDistribution`, `empiricalJoint`: the product of two mixed strategies, and the
  empirical joint distribution of `T` rounds of mixed play.

## Main results

- `empiricalJoint_isApproxCCE`: if both players have external regret at most `ε` on
  average, then the empirical joint distribution of their mixed play is an `ε`-CCE
  (row and column halves: `empiricalJoint_row_deviation_le`,
  `empiricalJoint_col_deviation_le`).
- `IsCoarseCorrelatedEquilibrium.toApprox`: an exact CCE is automatically an `ε`-CCE for
  every nonnegative `ε`.

## References

* [Rou13-L13] T. Roughgarden, *CS364A: Algorithmic Game Theory*, Lecture 13
  "Equilibria: Definitions, Examples, and Existence", Stanford, 2013.
* [Rou13-L17] T. Roughgarden, *CS364A: Algorithmic Game Theory*, Lecture 17
  "No-Regret Dynamics", Stanford, 2013.
* [CBL06] N. Cesa-Bianchi, G. Lugosi, *Prediction, Learning, and Games*,
  Cambridge University Press, 2006. Section 7.4.

Original formalization by Karim Abdel Sadek and Mark Bedaywi.
-/

open Finset BigOperators

/-! ## Two-Player Finite Games -/

/-- A finite two-player game with `M` row actions and `N` column actions, specified by
separate utility functions for the row and column players.  Both players are maximizers.
[Rou13-L13, §3.1]. Deviation: the source's games are cost-minimization games; here both
players maximize. -/
structure Game (M N : ℕ) where
  /-- The row player's utility at the action profile `(i, j)`. -/
  rowUtility : Fin M → Fin N → ℝ
  /-- The column player's utility at the action profile `(i, j)`. -/
  colUtility : Fin M → Fin N → ℝ

/-- The general two-player game underlying a zero-sum game: the row player's utility is
the payoff and the column player's utility is its negation. [Rou13-L13, §3.1 (there
cost-minimization; here both players maximize)]. -/
def ZeroSumGame.toGame {M N : ℕ} (G : ZeroSumGame M N) : Game M N where
  rowUtility := G.payoff
  colUtility i j := -G.payoff i j

/-! ## Joint Distributions -/

/-- A probability distribution over action profiles `Fin M × Fin N`, given as a
nonnegative weight for each profile `(i, j)` with total mass one. [Rou13-L13, Def. 3.4]. -/
structure JointDistribution (M N : ℕ) where
  /-- The probability of the action profile `(i, j)`. -/
  prob : Fin M → Fin N → ℝ
  /-- Every profile probability is nonnegative. -/
  nonneg : ∀ i j, 0 ≤ prob i j
  /-- The profile probabilities sum to one. -/
  sum_one : ∑ i : Fin M, ∑ j : Fin N, prob i j = 1

namespace JointDistribution

variable {M N : ℕ}

/-- The row marginal of a joint distribution: the probability that the row player plays
`i`, i.e. the sum of the profile probabilities `(i, j)` over columns `j`.
[Rou13-L13, Def. 3.4]. -/
noncomputable def rowMarginal (σ : JointDistribution M N) (i : Fin M) : ℝ :=
  ∑ j : Fin N, σ.prob i j

/-- The column marginal of a joint distribution: the probability that the column player
plays `j`, i.e. the sum of the profile probabilities `(i, j)` over rows `i`.
[Rou13-L13, Def. 3.4]. -/
noncomputable def colMarginal (σ : JointDistribution M N) (j : Fin N) : ℝ :=
  ∑ i : Fin M, σ.prob i j

/-- Row marginals are nonnegative because they are sums of nonnegative profile
probabilities. -/
lemma rowMarginal_nonneg (σ : JointDistribution M N) (i : Fin M) :
    0 ≤ σ.rowMarginal i :=
  Finset.sum_nonneg fun j _ => σ.nonneg i j

/-- Column marginals are nonnegative because they are sums of nonnegative profile
probabilities. -/
lemma colMarginal_nonneg (σ : JointDistribution M N) (j : Fin N) :
    0 ≤ σ.colMarginal j :=
  Finset.sum_nonneg fun i _ => σ.nonneg i j

/-- The row marginal is a probability distribution: its total mass is one. -/
lemma rowMarginal_sum_one (σ : JointDistribution M N) :
    ∑ i : Fin M, σ.rowMarginal i = 1 := by
  simpa [rowMarginal] using σ.sum_one

/-- The column marginal is a probability distribution: its total mass is one. -/
lemma colMarginal_sum_one (σ : JointDistribution M N) :
    ∑ j : Fin N, σ.colMarginal j = 1 := by
  simp only [colMarginal]
  rw [Finset.sum_comm]
  exact σ.sum_one

/-- The row player's expected utility under the joint distribution `σ`: the
`σ`-weighted sum of the row utilities over all action profiles. [Rou13-L13, Def. 3.4]. -/
noncomputable def rowExpectedUtility (σ : JointDistribution M N) (G : Game M N) : ℝ :=
  ∑ i : Fin M, ∑ j : Fin N, σ.prob i j * G.rowUtility i j

/-- The column player's expected utility under the joint distribution `σ`: the
`σ`-weighted sum of the column utilities over all action profiles. [Rou13-L13, Def. 3.4]. -/
noncomputable def colExpectedUtility (σ : JointDistribution M N) (G : Game M N) : ℝ :=
  ∑ i : Fin M, ∑ j : Fin N, σ.prob i j * G.colUtility i j

/-- The row player's expected utility from unilaterally deviating to the pure action
`i'` while the column player's action is still drawn from `σ`'s column marginal.
[Rou13-L13, §3]. -/
noncomputable def rowDeviationUtility (σ : JointDistribution M N) (G : Game M N)
    (i' : Fin M) : ℝ :=
  ∑ j : Fin N, σ.colMarginal j * G.rowUtility i' j

/-- The column player's expected utility from unilaterally deviating to the pure action
`j'` while the row player's action is still drawn from `σ`'s row marginal.
[Rou13-L13, §3]. -/
noncomputable def colDeviationUtility (σ : JointDistribution M N) (G : Game M N)
    (j' : Fin N) : ℝ :=
  ∑ i : Fin M, σ.rowMarginal i * G.colUtility i j'

end JointDistribution

/-! ## Coarse Correlated Equilibrium -/

/-- A joint distribution `σ` is a **coarse correlated equilibrium** of the two-player game
`G` if neither player can improve their expected utility by unilaterally committing in
advance to a fixed pure action: every row deviation utility is at most the row expected
utility, and likewise for the column player. [Rou13-L13, §3 (coarse correlated
equilibrium)]; [CBL06, §7.4]. Deviation: two players only, with utilities written as
explicit sums over `Fin M × Fin N`. -/
def IsCoarseCorrelatedEquilibrium {M N : ℕ} (G : Game M N)
    (σ : JointDistribution M N) : Prop :=
  (∀ i' : Fin M, σ.rowDeviationUtility G i' ≤ σ.rowExpectedUtility G) ∧
  (∀ j' : Fin N, σ.colDeviationUtility G j' ≤ σ.colExpectedUtility G)

/-- A joint distribution `σ` is an **ε-coarse correlated equilibrium** of `G` if each
unilateral commitment to a fixed pure action improves a player's expected utility by at
most `ε`. [Rou13-L13, §3]; [Rou13-L17, Prop. 3.1]; [CBL06, §7.4]. Deviation: two players only,
with utilities written as explicit sums over `Fin M × Fin N`. -/
def IsApproxCoarseCorrelatedEquilibrium {M N : ℕ} (G : Game M N)
    (σ : JointDistribution M N) (ε : ℝ) : Prop :=
  (∀ i' : Fin M, σ.rowDeviationUtility G i' ≤ σ.rowExpectedUtility G + ε) ∧
  (∀ j' : Fin N, σ.colDeviationUtility G j' ≤ σ.colExpectedUtility G + ε)

/-- An exact coarse correlated equilibrium is an `ε`-coarse correlated equilibrium for
every nonnegative `ε`. [Rou13-L13, §3]. -/
lemma IsCoarseCorrelatedEquilibrium.toApprox {M N : ℕ} {G : Game M N}
    {σ : JointDistribution M N} (h : IsCoarseCorrelatedEquilibrium G σ)
    {ε : ℝ} (hε : 0 ≤ ε) : IsApproxCoarseCorrelatedEquilibrium G σ ε :=
  ⟨fun i' => (h.1 i').trans (by linarith),
   fun j' => (h.2 j').trans (by linarith)⟩

/-! ## Product Distributions -/

/-- The product (independent) joint distribution of a row mixed strategy `p` and a column
mixed strategy `q`: the profile `(i, j)` has probability `p i · q j`. -/
noncomputable def productDistribution {M N : ℕ}
    (p : MixedStrategy M) (q : MixedStrategy N) : JointDistribution M N where
  prob i j := p.weights i * q.weights j
  nonneg i j := mul_nonneg (p.nonneg i) (q.nonneg j)
  sum_one := by
    have : ∀ i, ∑ j : Fin N, p.weights i * q.weights j = p.weights i := by
      intro i; rw [← Finset.mul_sum, q.sum_one, mul_one]
    simp_rw [this, p.sum_one]

/-- In a product distribution, the row marginal recovers the original row
mixed strategy. -/
@[simp] lemma productDistribution_rowMarginal {M N : ℕ}
    (p : MixedStrategy M) (q : MixedStrategy N) (i : Fin M) :
    (productDistribution p q).rowMarginal i = p.weights i := by
  show ∑ j : Fin N, p.weights i * q.weights j = p.weights i
  rw [← Finset.mul_sum, q.sum_one, mul_one]

/-- In a product distribution, the column marginal recovers the original column
mixed strategy. -/
@[simp] lemma productDistribution_colMarginal {M N : ℕ}
    (p : MixedStrategy M) (q : MixedStrategy N) (j : Fin N) :
    (productDistribution p q).colMarginal j = q.weights j := by
  show ∑ i : Fin M, p.weights i * q.weights j = q.weights j
  rw [← Finset.sum_mul, p.sum_one, one_mul]

/-! ## Empirical Joint Distribution from Mixed-Strategy Sequences -/

/-!
The empirical distribution records average play over time.  It is defined for
mixed strategies rather than sampled pure actions, so the probability of an
action profile `(i, j)` at round `t` is the product of the two round strategies.
-/

/-- The empirical joint distribution of `T > 0` rounds in which the row player plays the
mixed strategy `p t` and the column player plays the mixed strategy `q t`, drawing their
actions independently: the profile `(i, j)` has probability `(1/T) Σ_t p_t(i) · q_t(j)`.
[Rou13-L17, §3 (time-averaged history `σ`)].

**Proof sketch** (that the mass is one). Each round contributes a product distribution
of total mass one (`h_round_sum`, by summing out `q t` and then `p t`); pull the division
by `T` out of the double sum (`hPullDiv`), swap the time sum to the outside (`hSwap`),
and the total is `T · 1 / T = 1`. -/
noncomputable def empiricalJoint {M N T : ℕ} (hT : 0 < T)
    (p : Fin T → MixedStrategy M) (q : Fin T → MixedStrategy N) :
    JointDistribution M N where
  prob i j := (∑ t : Fin T, (p t).weights i * (q t).weights j) / T
  nonneg i j := div_nonneg
    (Finset.sum_nonneg fun t _ => mul_nonneg ((p t).nonneg i) ((q t).nonneg j))
    (Nat.cast_nonneg T)
  sum_one := by
    -- Each round contributes a product distribution of total mass one, so the
    -- time average also has total mass one.
    have hT_ne : (T : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hT)
    have h_round_sum : ∀ t : Fin T,
        ∑ i : Fin M, ∑ j : Fin N, (p t).weights i * (q t).weights j = 1 := by
      intro t
      calc ∑ i : Fin M, ∑ j : Fin N, (p t).weights i * (q t).weights j
          = ∑ i : Fin M, (p t).weights i * ∑ j : Fin N, (q t).weights j := by
            apply Finset.sum_congr rfl; intro i _
            rw [← Finset.mul_sum]
        _ = ∑ i : Fin M, (p t).weights i * 1 := by rw [(q t).sum_one]
        _ = 1 := by simp [(p t).sum_one]
    have hPullDiv :
        ∑ i : Fin M, ∑ j : Fin N,
            (∑ t : Fin T, (p t).weights i * (q t).weights j) / (T : ℝ) =
          (∑ i : Fin M, ∑ j : Fin N, ∑ t : Fin T,
              (p t).weights i * (q t).weights j) / (T : ℝ) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl; intro i _
      rw [Finset.sum_div]
    have hSwap :
        (∑ i : Fin M, ∑ j : Fin N, ∑ t : Fin T,
            (p t).weights i * (q t).weights j) =
          ∑ t : Fin T, ∑ i : Fin M, ∑ j : Fin N,
              (p t).weights i * (q t).weights j := by
      rw [show (∑ i : Fin M, ∑ j : Fin N, ∑ t : Fin T,
                (p t).weights i * (q t).weights j) =
            (∑ i : Fin M, ∑ t : Fin T, ∑ j : Fin N,
                (p t).weights i * (q t).weights j) from
            Finset.sum_congr rfl fun _ _ => Finset.sum_comm]
      exact Finset.sum_comm
    rw [hPullDiv, hSwap]
    simp_rw [h_round_sum]
    rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul, mul_one]
    exact div_self hT_ne

/-- The row marginal of the empirical joint distribution is the time-average
of the row mixed strategies. -/
@[simp] lemma empiricalJoint_rowMarginal {M N T : ℕ} (hT : 0 < T)
    (p : Fin T → MixedStrategy M) (q : Fin T → MixedStrategy N) (i : Fin M) :
    (empiricalJoint hT p q).rowMarginal i =
      (∑ t : Fin T, (p t).weights i) / T := by
  show ∑ j : Fin N,
      (∑ t : Fin T, (p t).weights i * (q t).weights j) / (T : ℝ) =
    (∑ t : Fin T, (p t).weights i) / (T : ℝ)
  rw [← Finset.sum_div, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl; intro t _
  rw [← Finset.mul_sum, (q t).sum_one, mul_one]

/-- The column marginal of the empirical joint distribution is the time-average
of the column mixed strategies. -/
@[simp] lemma empiricalJoint_colMarginal {M N T : ℕ} (hT : 0 < T)
    (p : Fin T → MixedStrategy M) (q : Fin T → MixedStrategy N) (j : Fin N) :
    (empiricalJoint hT p q).colMarginal j =
      (∑ t : Fin T, (q t).weights j) / T := by
  show ∑ i : Fin M,
      (∑ t : Fin T, (p t).weights i * (q t).weights j) / (T : ℝ) =
    (∑ t : Fin T, (q t).weights j) / (T : ℝ)
  rw [← Finset.sum_div, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl; intro t _
  rw [← Finset.sum_mul, (p t).sum_one, one_mul]

/-! ## Per-Round Expressions for Empirical Utilities -/

/-- Any utility-style sum `Σ_i Σ_j σ(i, j) · f(i, j)` over the empirical joint distribution
`σ = empiricalJoint hT p q` equals the time average `(1/T) Σ_t Σ_i Σ_j p_t(i) q_t(j) f(i, j)`
of the per-round expected values of `f`.

**Proof sketch.** Bookkeeping only: for each profile, move the factor `f i j` inside the
time sum (`hStep`); pull the division by `T` out of the double sum over profiles; then
swap the order of summation so time is outermost (two applications of `Finset.sum_comm`). -/
private lemma empiricalJoint_sum_prob_mul {M N T : ℕ} (hT : 0 < T)
    (p : Fin T → MixedStrategy M) (q : Fin T → MixedStrategy N)
    (f : Fin M → Fin N → ℝ) :
    (∑ i : Fin M, ∑ j : Fin N,
        (empiricalJoint hT p q).prob i j * f i j) =
      (∑ t : Fin T, ∑ i : Fin M, ∑ j : Fin N,
          (p t).weights i * (q t).weights j * f i j) / T := by
  -- This lemma is only bookkeeping: pull the division by `T` out of the finite
  -- sums, then swap the order of the time/action sums.
  show ∑ i : Fin M, ∑ j : Fin N,
        (∑ t : Fin T, (p t).weights i * (q t).weights j) / (T : ℝ) * f i j =
       (∑ t : Fin T, ∑ i : Fin M, ∑ j : Fin N,
          (p t).weights i * (q t).weights j * f i j) / (T : ℝ)
  have hStep : ∀ i : Fin M, ∀ j : Fin N,
      (∑ t : Fin T, (p t).weights i * (q t).weights j) / (T : ℝ) * f i j =
        (∑ t : Fin T, (p t).weights i * (q t).weights j * f i j) /
          (T : ℝ) := by
    intro i j
    rw [div_mul_eq_mul_div, ← Finset.sum_mul]
  simp_rw [hStep]
  rw [show (∑ i : Fin M, ∑ j : Fin N,
            (∑ t : Fin T, (p t).weights i * (q t).weights j * f i j) /
              (T : ℝ))
      = (∑ i : Fin M, ∑ j : Fin N, ∑ t : Fin T,
            (p t).weights i * (q t).weights j * f i j) / (T : ℝ) from ?_]
  · congr 1
    rw [show (∑ i : Fin M, ∑ j : Fin N, ∑ t : Fin T,
              (p t).weights i * (q t).weights j * f i j)
        = (∑ i : Fin M, ∑ t : Fin T, ∑ j : Fin N,
              (p t).weights i * (q t).weights j * f i j) from
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm]
    exact Finset.sum_comm
  · rw [Finset.sum_div]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.sum_div]

/-- The row player's expected utility under the empirical joint distribution is the time
average of the row player's per-round expected utilities `Σ_i Σ_j p_t(i) q_t(j) u(i, j)`. -/
lemma empiricalJoint_rowExpectedUtility {M N T : ℕ} (hT : 0 < T)
    (p : Fin T → MixedStrategy M) (q : Fin T → MixedStrategy N) (G : Game M N) :
    (empiricalJoint hT p q).rowExpectedUtility G =
      (∑ t : Fin T, ∑ i : Fin M, ∑ j : Fin N,
          (p t).weights i * (q t).weights j * G.rowUtility i j) / T :=
  empiricalJoint_sum_prob_mul hT p q G.rowUtility

/-- The column player's expected utility under the empirical joint distribution is the
time average of the column player's per-round expected utilities. -/
lemma empiricalJoint_colExpectedUtility {M N T : ℕ} (hT : 0 < T)
    (p : Fin T → MixedStrategy M) (q : Fin T → MixedStrategy N) (G : Game M N) :
    (empiricalJoint hT p q).colExpectedUtility G =
      (∑ t : Fin T, ∑ i : Fin M, ∑ j : Fin N,
          (p t).weights i * (q t).weights j * G.colUtility i j) / T :=
  empiricalJoint_sum_prob_mul hT p q G.colUtility

/-- The row player's deviation utility in the empirical joint distribution is the time
average `(1/T) Σ_t Σ_j q_t(j) u(i', j)` of the utility of always playing the fixed row
action `i'` against the column strategies actually played. -/
lemma empiricalJoint_rowDeviationUtility {M N T : ℕ} (hT : 0 < T)
    (p : Fin T → MixedStrategy M) (q : Fin T → MixedStrategy N) (G : Game M N)
    (i' : Fin M) :
    (empiricalJoint hT p q).rowDeviationUtility G i' =
      (∑ t : Fin T, ∑ j : Fin N, (q t).weights j * G.rowUtility i' j) / T := by
  unfold JointDistribution.rowDeviationUtility
  simp_rw [empiricalJoint_colMarginal]
  have hStep : ∀ j : Fin N,
      (∑ t : Fin T, (q t).weights j) / (T : ℝ) * G.rowUtility i' j =
        (∑ t : Fin T, (q t).weights j * G.rowUtility i' j) / (T : ℝ) := by
    intro j
    rw [div_mul_eq_mul_div, ← Finset.sum_mul]
  simp_rw [hStep]
  rw [← Finset.sum_div, Finset.sum_comm]

/-- The column player's deviation utility in the empirical joint distribution is the time
average `(1/T) Σ_t Σ_i p_t(i) v(i, j')` of the utility of always playing the fixed column
action `j'` against the row strategies actually played. -/
lemma empiricalJoint_colDeviationUtility {M N T : ℕ} (hT : 0 < T)
    (p : Fin T → MixedStrategy M) (q : Fin T → MixedStrategy N) (G : Game M N)
    (j' : Fin N) :
    (empiricalJoint hT p q).colDeviationUtility G j' =
      (∑ t : Fin T, ∑ i : Fin M, (p t).weights i * G.colUtility i j') / T := by
  unfold JointDistribution.colDeviationUtility
  simp_rw [empiricalJoint_rowMarginal]
  have hStep : ∀ i : Fin M,
      (∑ t : Fin T, (p t).weights i) / (T : ℝ) * G.colUtility i j' =
        (∑ t : Fin T, (p t).weights i * G.colUtility i j') / (T : ℝ) := by
    intro i
    rw [div_mul_eq_mul_div, ← Finset.sum_mul]
  simp_rw [hStep]
  rw [← Finset.sum_div, Finset.sum_comm]

/-! ## No-Regret Best-Response Dynamics Yield a CCE

If both players have small per-round external regret, then the empirical joint
distribution of their plays is an approximate coarse correlated equilibrium.
Specifically, suppose that for every round `t` the row player plays mixed
strategy `p t` and the column player plays `q t`, and that:

* (row regret bound) for every pure row deviation `i'`, the cumulative gain
  from switching to `i'` exceeds the row player's actual cumulative utility by
  at most `ε * T`;
* (column regret bound) similarly for the column player using `colUtility`.

Both inequalities are stated symmetrically because both players are maximizers
of their respective utility functions.  For a zero-sum game `G : ZeroSumGame
M N`, applying this theorem to `G.toGame` recovers the standard zero-sum
formulation. -/

/-- Row half of `empiricalJoint_isApproxCCE`: if the row player's cumulative external
regret against the fixed deviation `i'` (the cumulative utility of always playing `i'`
minus the actual cumulative expected utility) is at most `ε · T`, then in the empirical
joint distribution deviating to `i'` gains at most `ε` over the expected utility.
[Rou13-L17, Prop. 3.1]; [CBL06, §7.4].

**Proof sketch.** Step 1: rewrite both empirical utilities as time averages
(`empiricalJoint_rowDeviationUtility`, `empiricalJoint_rowExpectedUtility`). Step 2: put
the right-hand side over the common denominator `T`. Step 3: clear `T > 0` from both
sides; the resulting inequality is the regret hypothesis. -/
lemma empiricalJoint_row_deviation_le {M N T : ℕ} (hT : 0 < T)
    (G : Game M N)
    (p : Fin T → MixedStrategy M) (q : Fin T → MixedStrategy N)
    (ε : ℝ) (i' : Fin M)
    (hRow : (∑ t : Fin T, ∑ j : Fin N, (q t).weights j * G.rowUtility i' j) -
        (∑ t : Fin T, ∑ i : Fin M, ∑ j : Fin N,
          (p t).weights i * (q t).weights j * G.rowUtility i j) ≤ ε * T) :
    (empiricalJoint hT p q).rowDeviationUtility G i' ≤
      (empiricalJoint hT p q).rowExpectedUtility G + ε := by
  have hT_pos : (0 : ℝ) < (T : ℝ) := Nat.cast_pos.mpr hT
  have hT_ne : (T : ℝ) ≠ 0 := ne_of_gt hT_pos
  -- Step 1: rewrite both empirical utilities as time averages.
  rw [empiricalJoint_rowDeviationUtility, empiricalJoint_rowExpectedUtility]
  -- Step 2: put the right-hand side over the common denominator `T`.
  have hRHS :
      (∑ t : Fin T, ∑ i : Fin M, ∑ j : Fin N,
          (p t).weights i * (q t).weights j * G.rowUtility i j) / (T : ℝ) +
        ε =
        ((∑ t : Fin T, ∑ i : Fin M, ∑ j : Fin N,
          (p t).weights i * (q t).weights j * G.rowUtility i j) +
          ε * (T : ℝ)) / (T : ℝ) := by field_simp
  -- Step 3: clear `T` and conclude from the regret bound.
  rw [hRHS, div_le_div_iff₀ hT_pos hT_pos]
  nlinarith [hRow, hT_pos]

/-- Column half of `empiricalJoint_isApproxCCE`: if the column player's cumulative
external regret against the fixed deviation `j'` is at most `ε · T`, then in the
empirical joint distribution deviating to `j'` gains at most `ε`. The mirror image of
`empiricalJoint_row_deviation_le`, with the same three steps. [Rou13-L17, Prop. 3.1];
[CBL06, §7.4].

**Proof sketch.** Step 1: rewrite both empirical utilities as time averages
(`empiricalJoint_colDeviationUtility`, `empiricalJoint_colExpectedUtility`). Step 2: put
the right-hand side over the common denominator `T`. Step 3: clear `T > 0` from both
sides; the resulting inequality is the regret hypothesis. -/
lemma empiricalJoint_col_deviation_le {M N T : ℕ} (hT : 0 < T)
    (G : Game M N)
    (p : Fin T → MixedStrategy M) (q : Fin T → MixedStrategy N)
    (ε : ℝ) (j' : Fin N)
    (hCol : (∑ t : Fin T, ∑ i : Fin M, (p t).weights i * G.colUtility i j') -
        (∑ t : Fin T, ∑ i : Fin M, ∑ j : Fin N,
          (p t).weights i * (q t).weights j * G.colUtility i j) ≤ ε * T) :
    (empiricalJoint hT p q).colDeviationUtility G j' ≤
      (empiricalJoint hT p q).colExpectedUtility G + ε := by
  have hT_pos : (0 : ℝ) < (T : ℝ) := Nat.cast_pos.mpr hT
  have hT_ne : (T : ℝ) ≠ 0 := ne_of_gt hT_pos
  -- Step 1: rewrite both empirical utilities as time averages.
  rw [empiricalJoint_colDeviationUtility, empiricalJoint_colExpectedUtility]
  -- Step 2: put the right-hand side over the common denominator `T`.
  have hRHS :
      (∑ t : Fin T, ∑ i : Fin M, ∑ j : Fin N,
          (p t).weights i * (q t).weights j * G.colUtility i j) / (T : ℝ) +
        ε =
        ((∑ t : Fin T, ∑ i : Fin M, ∑ j : Fin N,
          (p t).weights i * (q t).weights j * G.colUtility i j) +
          ε * (T : ℝ)) / (T : ℝ) := by field_simp
  -- Step 3: clear `T` and conclude from the regret bound.
  rw [hRHS, div_le_div_iff₀ hT_pos hT_pos]
  nlinarith [hCol, hT_pos]

/-- No-regret dynamics yield a coarse correlated equilibrium: if over `T > 0` rounds of
mixed play `p t`, `q t` both players have cumulative external regret at most `ε · T`
against every fixed pure deviation (i.e. average regret at most `ε`), then the empirical
joint distribution of their play is an `ε`-coarse correlated equilibrium of `G`.
[Rou13-L17, Prop. 3.1 (no-regret dynamics converge to CCE)]; [CBL06, §7.4]. Deviation:
stated for two players, with the regret hypotheses given as cumulative bounds `ε · T` for
each player (the source's Proposition 3.1 states the hypothesis as time-averaged regret at
most `ε` for every player and deviation; here it is written as the equivalent cumulative
bound `ε · T`).

**Proof sketch.** The proof is the term `⟨row, col⟩`: the row half is
`empiricalJoint_row_deviation_le` applied to the row regret hypothesis at each deviation
`i'`, and the column half is `empiricalJoint_col_deviation_le` applied to the column
regret hypothesis at each deviation `j'`. Each half rewrites both sides as time averages,
puts them over the common denominator `T`, clears `T`, and reads off the regret bound. -/
theorem empiricalJoint_isApproxCCE {M N T : ℕ} (hT : 0 < T)
    (G : Game M N)
    (p : Fin T → MixedStrategy M) (q : Fin T → MixedStrategy N)
    (ε : ℝ)
    (hRow : ∀ i' : Fin M,
      (∑ t : Fin T, ∑ j : Fin N, (q t).weights j * G.rowUtility i' j) -
        (∑ t : Fin T, ∑ i : Fin M, ∑ j : Fin N,
          (p t).weights i * (q t).weights j * G.rowUtility i j) ≤ ε * T)
    (hCol : ∀ j' : Fin N,
      (∑ t : Fin T, ∑ i : Fin M, (p t).weights i * G.colUtility i j') -
        (∑ t : Fin T, ∑ i : Fin M, ∑ j : Fin N,
          (p t).weights i * (q t).weights j * G.colUtility i j) ≤ ε * T) :
    IsApproxCoarseCorrelatedEquilibrium G (empiricalJoint hT p q) ε :=
  -- Step 1: row half.  Step 2: column half.
  ⟨fun i' => empiricalJoint_row_deviation_le hT G p q ε i' (hRow i'),
   fun j' => empiricalJoint_col_deviation_le hT G p q ε j' (hCol j')⟩
