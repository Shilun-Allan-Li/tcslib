/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Probability
import TCSlib.Cryptography.Foundations.Probability

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false
attribute [local irreducible] TCSlib.Cryptography.Games.OracleComp.bind TCSlib.Cryptography.Games.ProbComp.expect TCSlib.Cryptography.Games.ProbComp.prob TCSlib.Cryptography.Games.ProbComp.sample

/-!
# Advantages of game-playing adversaries

Security definitions come in three shapes, each measured at one value of the security parameter:
- a **search game** (forge a tag, find a collision, invert a function): its advantage is the
  probability that the game, run with the adversary, outputs `true`;
- a **distinguishing pair** (real versus random, left versus right): its advantage is the
  difference of the two games' acceptance probabilities;
- a **guess-the-bit game**: a bit `b` is drawn, the game runs on `b`, and the adversary wins if it
  outputs `b`. Its advantage is the distance of the winning probability from `½`, which is half
  the distinguishing advantage of the two games (`guessAdv_eq_half_advantage`).

Games are `ProbComp Bool`s built from the adversary; these shapes are what asymptotic security
definitions wrap with "negligible for every efficient adversary".

## Main definitions

* `Games.accept G`: the probability that `G` outputs `true`.
* `Games.advantage G₀ G₁`: `|Pr[G₀ = 1] − Pr[G₁ = 1]|`.
* `Games.guessGame G`, `Games.guessAdv G`: the guess-the-bit game over `G : Bool → ProbComp Bool`
  and its advantage `|Pr[win] − ½|`.

## Main results

* `advantage_triangle`, `advantage_hybrid`, `exists_advantage_hybrid_gap`: the hybrid argument;
  the advantage between the ends of a chain of games is at most the sum of the advantages between
  neighbours, so some neighbouring pair carries a `1/n` share of it, for `n` hops
  ([PS10, Lemma 71.6]).
* `guessAdv_eq_half_advantage`: the guess-the-bit advantage is half the distinguishing advantage
  between the games for `b = 1` and `b = 0` (the identity behind [PS10, Lemma 73.8]).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §3.1 (Def 69.4, computational indistinguishability), Lemma 71.6 (the hybrid lemma), Lemma 73.8
  (the prediction lemma) and Definition 168.1 (the experiments `IND_b` for a fixed challenge bit).
* [VCVio] D. Tuma and the VCVio contributors, *VCVio: machine-checked cryptographic proofs in
  Lean*, https://github.com/dtumad/VCV-io, commit 9054989327a7185ff19ef9ff0f119cccea479501
  (2026-11-04), Apache License 2.0. Design adapted (no code transcribed): oracle specifications
  indexed by a type of oracle names (`VCVio/OracleComp/OracleSpec.lean`), oracle computations as
  a free monad over them (`OracleComp.lean`, `OracleQuery.lean`), probabilistic computations as
  computations over the uniform-selection oracles (`OracleComp/ProbComp/Basic.lean`), and
  simulation of oracles by stateful handlers with query logging and composition (`SimSemantics/`,
  `SimSemantics/QueryImpl/Compose.lean`, `QueryTracking/LoggingOracle`).
-/

namespace TCSlib.Cryptography.Games

open Finset ProbComp

/-- The probability that the game `G` outputs `true`. -/
noncomputable def accept (G : ProbComp Bool) : ℝ := prob G (· = true)

/-- The acceptance probability is the probability of the output `true`:
`accept G = prob G (· = true)`. -/
theorem accept_eq (G : ProbComp Bool) : accept G = prob G (· = true) :=
  rfl

/-- The **distinguishing advantage** between two games: `|Pr[G₀ = 1] − Pr[G₁ = 1]|`.
[PS10, §3.1] -/
noncomputable def advantage (G₀ G₁ : ProbComp Bool) : ℝ := |accept G₀ - accept G₁|

/-- The distinguishing advantage is the absolute gap of the acceptance probabilities:
`advantage G₀ G₁ = |accept G₀ - accept G₁|`. -/
theorem advantage_eq (G₀ G₁ : ProbComp Bool) : advantage G₀ G₁ = |accept G₀ - accept G₁| :=
  rfl

/-- An acceptance probability is nonnegative. -/
theorem accept_nonneg (G : ProbComp Bool) : 0 ≤ accept G := prob_nonneg G _

/-- An acceptance probability is at most one. -/
theorem accept_le_one (G : ProbComp Bool) : accept G ≤ 1 := prob_le_one G _

/-- The distinguishing advantage is nonnegative. -/
theorem advantage_nonneg (G₀ G₁ : ProbComp Bool) : 0 ≤ advantage G₀ G₁ := abs_nonneg _

/-- The distinguishing advantage is symmetric. -/
theorem advantage_comm (G₀ G₁ : ProbComp Bool) : advantage G₀ G₁ = advantage G₁ G₀ :=
  abs_sub_comm _ _

/-- A game has no advantage against itself. -/
@[simp] theorem advantage_self (G : ProbComp Bool) : advantage G G = 0 := by simp [advantage]

/-- The distinguishing advantage is at most one. -/
theorem advantage_le_one (G₀ G₁ : ProbComp Bool) : advantage G₀ G₁ ≤ 1 := by
  unfold advantage
  rw [abs_le]
  constructor <;> linarith [accept_nonneg G₀, accept_nonneg G₁, accept_le_one G₀, accept_le_one G₁]

/-- **One game hop:** the advantage between `G₀` and `G₂` is at most the sum of the advantages
through `G₁`. -/
theorem advantage_triangle (G₀ G₁ G₂ : ProbComp Bool) :
    advantage G₀ G₂ ≤ advantage G₀ G₁ + advantage G₁ G₂ :=
  abs_sub_le _ _ _

/-- **The hybrid argument:** along a chain of games `G 0, …, G n`, the advantage between the ends
is at most the sum of the advantages between neighbours: the telescoping inequality in the proof of
[PS10, Lemma 71.6]. It is the concrete layer's `abs_sub_le_sum_hybrids` for the acceptance
probabilities. -/
theorem advantage_hybrid (G : ℕ → ProbComp Bool) (n : ℕ) :
    advantage (G 0) (G n) ≤ ∑ i ∈ range n, advantage (G i) (G (i + 1)) :=
  abs_sub_le_sum_hybrids (fun i => accept (G i)) n

/-- **The hybrid lemma:** along a chain `G 0, …, G n` of `n > 0` hops (`n + 1` games), some
neighbouring pair has advantage at least `advantage (G 0) (G n) / n`. [PS10, Lemma 71.6]

**Deviation:** sharper than the source, which takes `m` distributions (`m − 1` hops), a threshold
`ε < |g₁ − g_m|`, and concludes `> ε/m`. Here the divisor is the number of hops and the bound is
the exact endpoint advantage; the source's form follows with `m = n + 1`. It is the concrete
layer's `exists_hybrid_gap` for the acceptance probabilities. -/
theorem exists_advantage_hybrid_gap (G : ℕ → ProbComp Bool) {n : ℕ} (hn : 0 < n) :
    ∃ i < n, advantage (G 0) (G n) / n ≤ advantage (G i) (G (i + 1)) :=
  exists_hybrid_gap (fun i => accept (G i)) hn

/-! ### Guess-the-bit games -/

/-- The **guess-the-bit game** over `G`: draw a uniform bit `b`, run `G b`, and win if its output
is `b`: the prediction experiment `b ← {0,1}; t ← X^b : A(t) = b` of [PS10, Lemma 73.8], with
`G b` the whole game for challenge bit `b`. -/
noncomputable def guessGame (G : Bool → ProbComp Bool) : ProbComp Bool :=
  (sample Bool).bind fun b => (G b).bind fun b' => .pure (decide (b' = b))

/-- The guess-the-bit game samples `b`, runs `G b` and outputs whether it returned `b`:
`guessGame G = (sample Bool).bind fun b => (G b).bind fun b' => .pure (decide (b' = b))`. -/
theorem guessGame_eq (G : Bool → ProbComp Bool) :
    guessGame G = (sample Bool).bind fun b => (G b).bind fun b' => .pure (decide (b' = b)) :=
  rfl

/-- The **guess-the-bit advantage**: how far the winning probability is from `½`. -/
noncomputable def guessAdv (G : Bool → ProbComp Bool) : ℝ := |accept (guessGame G) - 1 / 2|

/-- The winning probability of the guess-the-bit game is the average of `Pr[G 1 = 1]` and
`Pr[G 0 = 0]`. [PS10, proof of Lemma 73.8]

**Proof sketch.** Total probability over the uniform bit (two equally likely values), and
`Pr[G 0 = 0] = 1 − Pr[G 0 = 1]`. -/
theorem accept_guessGame (G : Bool → ProbComp Bool) :
    accept (guessGame G) = (accept (G true) + (1 - accept (G false))) / 2 := by
  classical
  have hnot : prob (G false) (· = false) = 1 - accept (G false) := by
    rw [accept, ← prob_not]
    exact prob_congr _ fun b => by cases b <;> simp
  unfold accept guessGame
  rw [prob_bind, expect_sample]
  simp only [Fintype.univ_bool, mem_singleton, Bool.true_eq_false, not_false_eq_true,
    sum_insert, sum_singleton, Fintype.card_bool, prob_bind]
  have h1 : expect (G true) (fun b' => prob (OracleComp.pure (decide (b' = true))) (· = true)) =
      prob (G true) (· = true) := by
    rw [prob_eq_expect]; congr 1; funext b'; cases b' <;> simp [prob_pure]
  have h0 : expect (G false) (fun b' => prob (OracleComp.pure (decide (b' = false))) (· = true)) =
      prob (G false) (· = false) := by
    rw [prob_eq_expect]; congr 1; funext b'; cases b' <;> simp [prob_pure]
  rw [h1, h0, hnot]
  simp only [accept]
  push_cast
  ring

/-- **Guessing versus distinguishing:** `|Pr[win] − ½| = |Pr[G 1 = 1] − Pr[G 0 = 1]| / 2`. This
is the identity behind [PS10, §3.1.1, Lemma 73.8]: a predictor with success `½ + δ` is a
distinguisher with advantage `2δ`, and conversely.

**Deviation:** stated exactly, at one value of the security parameter, for whole games; the
absolute value replaces the source's "without loss of generality" complement of the distinguisher.
[PS10, Def 168.1] is stated in the distinguishing form only, with its experiments `IND_0`, `IND_1`
as the games `G false`, `G true`. The concrete layer's counterpart is `predict_eq`
(`TCSlib.Cryptography.Asymptotic.Ensembles`). -/
theorem guessAdv_eq_half_advantage (G : Bool → ProbComp Bool) :
    guessAdv G = advantage (G true) (G false) / 2 := by
  unfold guessAdv advantage
  rw [accept_guessGame]
  rw [show (accept (G true) + (1 - accept (G false))) / 2 - 1 / 2 =
      (accept (G true) - accept (G false)) / 2 by ring, abs_div, abs_two]

end TCSlib.Cryptography.Games
