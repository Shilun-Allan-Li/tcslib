/-
Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karim Abdel Sadek, Mark Bedaywi
-/
import TCSlib.LearningTheory.Minimax.FiniteMinimax

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

open Finset BigOperators

/-!
# Coarse Correlated Equilibria

## Main results

- `empiricalJoint_isApproxCCE`: if both players have external regret at most `ε` on average, then the empirical joint distribution of their mixed play is an `ε`-CCE
- `IsCoarseCorrelatedEquilibrium.toApprox`: an exact CCE is automatically an `ε`-CCE for every nonnegative `ε`

## References

- Original formalization by Karim Abdel Sadek, Mark Bedaywi
-/

/-! ## Two-Player Finite Games -/

/-- A finite two-player game specified by separate utility functions for the
row and column players.  Both players are maximizers. -/
structure Game (M N : ℕ) where
  rowUtility : Fin M → Fin N → ℝ
  colUtility : Fin M → Fin N → ℝ

/-- Embed a zero-sum game into the general two-player game framework: the row
player maximizes the payoff and the column player maximizes its negation. -/
def ZeroSumGame.toGame {M N : ℕ} (G : ZeroSumGame M N) : Game M N where
  rowUtility := G.payoff
  colUtility i j := -G.payoff i j

/-! ## Joint Distributions -/

/-- A probability distribution over action profiles `Fin M × Fin N`. -/
structure JointDistribution (M N : ℕ) where
  prob : Fin M → Fin N → ℝ
  nonneg : ∀ i j, 0 ≤ prob i j
  sum_one : ∑ i : Fin M, ∑ j : Fin N, prob i j = 1

namespace JointDistribution

variable {M N : ℕ}

/-- The row marginal: probability that the row player plays `i`. -/
noncomputable def rowMarginal (σ : JointDistribution M N) (i : Fin M) : ℝ :=
  ∑ j : Fin N, σ.prob i j

/-- The column marginal: probability that the column player plays `j`. -/
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

/-- Row player's expected utility under `σ`. -/
noncomputable def rowExpectedUtility (σ : JointDistribution M N) (G : Game M N) : ℝ :=
  ∑ i : Fin M, ∑ j : Fin N, σ.prob i j * G.rowUtility i j

/-- Column player's expected utility under `σ`. -/
noncomputable def colExpectedUtility (σ : JointDistribution M N) (G : Game M N) : ℝ :=
  ∑ i : Fin M, ∑ j : Fin N, σ.prob i j * G.colUtility i j

/-- Row player's expected utility from unilaterally deviating to pure action
`i'` (the column player keeps `σ`'s column marginal). -/
noncomputable def rowDeviationUtility (σ : JointDistribution M N) (G : Game M N)
    (i' : Fin M) : ℝ :=
  ∑ j : Fin N, σ.colMarginal j * G.rowUtility i' j

/-- Column player's expected utility from unilaterally deviating to pure action
`j'` (the row player keeps `σ`'s row marginal). -/
noncomputable def colDeviationUtility (σ : JointDistribution M N) (G : Game M N)
    (j' : Fin N) : ℝ :=
  ∑ i : Fin M, σ.rowMarginal i * G.colUtility i j'

end JointDistribution

/-! ## Coarse Correlated Equilibrium -/

/-- A **coarse correlated equilibrium** of a two-player game `G`: neither
player can improve their expected utility by unilaterally committing in advance
to a fixed pure action. -/
def IsCoarseCorrelatedEquilibrium {M N : ℕ} (G : Game M N)
    (σ : JointDistribution M N) : Prop :=
  (∀ i' : Fin M, σ.rowDeviationUtility G i' ≤ σ.rowExpectedUtility G) ∧
  (∀ j' : Fin N, σ.colDeviationUtility G j' ≤ σ.colExpectedUtility G)

/-- An **ε-coarse correlated equilibrium**: each unilateral deviation can
improve a player's expected utility by at most `ε`. -/
def IsApproxCoarseCorrelatedEquilibrium {M N : ℕ} (G : Game M N)
    (σ : JointDistribution M N) (ε : ℝ) : Prop :=
  (∀ i' : Fin M, σ.rowDeviationUtility G i' ≤ σ.rowExpectedUtility G + ε) ∧
  (∀ j' : Fin N, σ.colDeviationUtility G j' ≤ σ.colExpectedUtility G + ε)

/-- An exact CCE is automatically an `ε`-CCE for every nonnegative `ε`. -/
lemma IsCoarseCorrelatedEquilibrium.toApprox {M N : ℕ} {G : Game M N}
    {σ : JointDistribution M N} (h : IsCoarseCorrelatedEquilibrium G σ)
    {ε : ℝ} (hε : 0 ≤ ε) : IsApproxCoarseCorrelatedEquilibrium G σ ε :=
  ⟨fun i' => (h.1 i').trans (by linarith),
   fun j' => (h.2 j').trans (by linarith)⟩

/-! ## Product Distributions -/

/-- The product (independent) joint distribution of two mixed strategies. -/
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

/-- The empirical joint distribution of `T` rounds in which the row player plays
mixed strategy `p t` and the column player plays mixed strategy `q t`, drawing
their actions independently. -/
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

/-- Helper: any utility-style sum `∑ i ∑ j σ.prob i j * f i j` over the empirical
joint distribution is the time-average of the per-round expected values
of `f`. -/
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

/-- Row expected utility under the empirical joint distribution is the average
of the row player's per-round expected utilities. -/
lemma empiricalJoint_rowExpectedUtility {M N T : ℕ} (hT : 0 < T)
    (p : Fin T → MixedStrategy M) (q : Fin T → MixedStrategy N) (G : Game M N) :
    (empiricalJoint hT p q).rowExpectedUtility G =
      (∑ t : Fin T, ∑ i : Fin M, ∑ j : Fin N,
          (p t).weights i * (q t).weights j * G.rowUtility i j) / T :=
  empiricalJoint_sum_prob_mul hT p q G.rowUtility

/-- Column expected utility under the empirical joint distribution is the
average of the column player's per-round expected utilities. -/
lemma empiricalJoint_colExpectedUtility {M N T : ℕ} (hT : 0 < T)
    (p : Fin T → MixedStrategy M) (q : Fin T → MixedStrategy N) (G : Game M N) :
    (empiricalJoint hT p q).colExpectedUtility G =
      (∑ t : Fin T, ∑ i : Fin M, ∑ j : Fin N,
          (p t).weights i * (q t).weights j * G.colUtility i j) / T :=
  empiricalJoint_sum_prob_mul hT p q G.colUtility

/-- The row player's deviation utility in the empirical distribution is the
time-average utility of always playing the fixed row action `i'`. -/
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

/-- The column player's deviation utility in the empirical distribution is the
time-average utility of always playing the fixed column action `j'`. -/
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

/-- If both players have external regret at most `ε` on average, then the
empirical joint distribution of their mixed play is an `ε`-CCE. -/
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
    IsApproxCoarseCorrelatedEquilibrium G (empiricalJoint hT p q) ε := by
  have hT_pos : (0 : ℝ) < (T : ℝ) := Nat.cast_pos.mpr hT
  have hT_ne : (T : ℝ) ≠ 0 := ne_of_gt hT_pos
  refine ⟨?_, ?_⟩
  · intro i'
    -- Rewrite empirical utilities as time averages, then divide the row regret
    -- inequality by the positive horizon length.
    rw [empiricalJoint_rowDeviationUtility, empiricalJoint_rowExpectedUtility]
    have h := hRow i'
    have hRHS :
        (∑ t : Fin T, ∑ i : Fin M, ∑ j : Fin N,
            (p t).weights i * (q t).weights j * G.rowUtility i j) / (T : ℝ) +
          ε =
          ((∑ t : Fin T, ∑ i : Fin M, ∑ j : Fin N,
            (p t).weights i * (q t).weights j * G.rowUtility i j) +
            ε * (T : ℝ)) / (T : ℝ) := by field_simp
    rw [hRHS, div_le_div_iff₀ hT_pos hT_pos]
    nlinarith [h, hT_pos]
  · intro j'
    -- The column side is identical, using the column regret hypothesis.
    rw [empiricalJoint_colDeviationUtility, empiricalJoint_colExpectedUtility]
    have h := hCol j'
    have hRHS :
        (∑ t : Fin T, ∑ i : Fin M, ∑ j : Fin N,
            (p t).weights i * (q t).weights j * G.colUtility i j) / (T : ℝ) +
          ε =
          ((∑ t : Fin T, ∑ i : Fin M, ∑ j : Fin N,
            (p t).weights i * (q t).weights j * G.colUtility i j) +
            ε * (T : ℝ)) / (T : ℝ) := by field_simp
    rw [hRHS, div_le_div_iff₀ hT_pos hT_pos]
    nlinarith [h, hT_pos]
