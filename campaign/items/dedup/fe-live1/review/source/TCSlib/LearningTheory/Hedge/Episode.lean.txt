/-
Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karim Abdel Sadek, Mark Bedaywi
-/

import TCSlib.LearningTheory.Hedge.Regret

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Adaptive Episodes for Hedge

The online interaction model behind the Hedge bound: a learner policy chooses a mixed
strategy from the past losses, an adaptive (nonoblivious) adversary chooses the next loss
vector after seeing that strategy, and the two generate a loss sequence by recursion
[CBL06, §4.1].  Deviation from CBL: the adversary sees the learner's mixed strategy but not
a random draw from it, and no randomness is modeled at all, because Hedge's regret bound
`hedge_regret_bound_tight` is pathwise for the expected loss and therefore applies to the
generated sequence directly.

## Main definitions

- `LossHistory`, `LossHistory.toLossSeq`: finite loss histories and their reading as
  loss sequences.
- `LearnerPolicy`, `AdaptiveAdversary`: history-dependent learners and nonanticipating
  adversaries.
- `hedgePolicy`: Hedge as a learner policy.
- `episodeLossNat`, `episodeLossSeq`, `Episode`, `Episode.generated`: the generated
  interaction and its packaging.

## Main results

- `episodeLossSeq_valid`: The realized loss sequence of any generated learner/adversary
  episode is valid.
- `Episode.losses_valid`: The loss sequence stored by an `Episode` is valid.
- `hedge_regret_bound_tight_episode`: Hedge's tight regret bound stated over generated
  adaptive episodes.
- `hedge_regret_bound_tight_of_episode`: The tight regret bound for a packaged `Episode`
  whose learner is Hedge.

## References

* [CBL06] N. Cesa-Bianchi, G. Lugosi, *Prediction, Learning, and Games*, Cambridge
  University Press, 2006.
* [FS97] Y. Freund, R. E. Schapire, "A decision-theoretic generalization of on-line
  learning and an application to boosting", *J. Comput. Syst. Sci.* 55(1):119–139, 1997.

Original formalization by Karim Abdel Sadek and Mark Bedaywi.
-/

open Real Finset BigOperators

/-! ## Histories, Policies, and Adversaries -/

/-- The type of length-`t` histories of loss vectors for `N` experts: a history records only
past losses, so at time `t` its domain is `Fin t` and there is no entry for the current or
future rounds. -/
def LossHistory (N : ℕ) (t : ℕ) := Fin t → Fin N → ℝ

namespace LossHistory

/-- A history of length `t` regarded as the loss sequence over `t` rounds (the identity on
the underlying function).  This coercion-style helper lets us reuse the definitions from
`Hedge.Basic`, which are stated for finite loss sequences. -/
def toLossSeq {N t : ℕ} (history : LossHistory N t) : LossSeq N t :=
  history

end LossHistory

/-- A learner policy maps every past loss history to a mixed strategy (a probability vector)
over the `N` experts [CBL06, §4.1].  The policy is deterministic: once the past loss table is
fixed, it returns the distribution used for the next round. -/
structure LearnerPolicy (N : ℕ) [NeZero N] where
  /-- The distribution chosen after seeing a history of length `t`. -/
  weights : (t : ℕ) → LossHistory N t → Fin N → ℝ
  /-- Each coordinate of the chosen distribution is nonnegative. -/
  nonneg : ∀ t history i, 0 ≤ weights t history i
  /-- The distribution has total mass one. -/
  sum_one : ∀ t history, ∑ i : Fin N, weights t history i = 1

/-- An adaptive adversary maps the past loss history and the learner's current distribution
to the next loss vector, with every loss in `[0, 1]` [CBL06, §4.1 (nonoblivious opponent)].
It is adaptive but nonanticipating: it sees the past and the current mixed strategy, then
chooses the whole loss vector for this round.  Deviation: it does not see a sampled expert
action, since no randomness is modeled. -/
structure AdaptiveAdversary (N : ℕ) where
  /-- The loss vector selected at time `t` after observing history and distribution. -/
  loss : (t : ℕ) → LossHistory N t → (Fin N → ℝ) → Fin N → ℝ
  /-- Every selected loss coordinate is bounded between zero and one. -/
  valid : ∀ t history p i, 0 ≤ loss t history p i ∧ loss t history p i ≤ 1

/-! ## Hedge as a Learner Policy -/

/-- Hedge with learning rate `η` as a history-dependent learner policy: after a history of
length `t`, it plays the Hedge distribution `hedgeDist η · t` computed from the realized past
losses [CBL06, §4.1]; [FS97, §2].  This is the same `hedgeDist` as in the pathwise theorem. -/
noncomputable def hedgePolicy (N : ℕ) [NeZero N] (η : ℝ) : LearnerPolicy N where
  weights t history i := hedgeDist η history.toLossSeq t i
  nonneg t history i := hedgeDist_nonneg η history.toLossSeq t i
  sum_one t history := hedgeDist_sum η history.toLossSeq t

/-! ## Generated Episodes -/

/-- The loss vector produced at natural time `t` by running a learner policy against an
adaptive adversary [CBL06, §4.1].  This is the online recursion: to compute the loss vector
at time `t`, first expose to the adversary the already generated prefix of length `t`, then
pass the learner's distribution for that same prefix. -/
def episodeLossNat {N : ℕ} [NeZero N]
    (learner : LearnerPolicy N) (adversary : AdaptiveAdversary N) :
    (t : ℕ) → Fin N → ℝ
  | t =>
      -- The recursive call is only used on `s : Fin t`, so the adversary at
      -- time `t` sees exactly the already-generated prefix of length `t`.
      adversary.loss t
        (fun s : Fin t => episodeLossNat learner adversary s.val)
        (learner.weights t (fun s : Fin t => episodeLossNat learner adversary s.val))
termination_by t => t
decreasing_by
  all_goals simp

/-- The finite loss sequence realized over `T` rounds by a learner/adversary pair
[CBL06, §4.1]: the natural-time recursion `episodeLossNat` restricted to the first `T`
rounds, which is the shape the pathwise Hedge theorem expects. -/
def episodeLossSeq {N : ℕ} [NeZero N] (T : ℕ)
    (learner : LearnerPolicy N) (adversary : AdaptiveAdversary N) : LossSeq N T :=
  fun t i => episodeLossNat learner adversary t.val i

/-- A finite episode packages a learner, an adversary, and the realized loss sequence over
`T` rounds of their interaction [CBL06, §4.1].  The consistency condition says that the
stored loss sequence is the one generated by the online recursion `episodeLossSeq`.  The
structure is useful when we want to talk about an episode as data. -/
structure Episode (N T : ℕ) [NeZero N] where
  /-- The learner policy. -/
  learner : LearnerPolicy N
  /-- The adaptive adversary. -/
  adversary : AdaptiveAdversary N
  /-- The realized loss sequence over the `T` rounds. -/
  losses : LossSeq N T
  /-- The stored losses are exactly those generated by running the learner against the
  adversary. -/
  losses_eq_generated :
    losses = episodeLossSeq T learner adversary

/-- The canonical episode of a learner/adversary pair: the one whose losses are obtained by
running the recursion `episodeLossSeq`. -/
def Episode.generated {N T : ℕ} [NeZero N]
    (learner : LearnerPolicy N) (adversary : AdaptiveAdversary N) : Episode N T where
  learner := learner
  adversary := adversary
  losses := episodeLossSeq T learner adversary
  losses_eq_generated := rfl

/-- The loss sequence generated by any learner/adversary pair is valid (all losses in
`[0,1]`).  Validity is inherited directly from the adversary's range condition. -/
theorem episodeLossSeq_valid {N T : ℕ} [NeZero N]
    (learner : LearnerPolicy N) (adversary : AdaptiveAdversary N) :
    (episodeLossSeq T learner adversary).Valid := by
  intro t i
  dsimp [episodeLossSeq]
  -- Unfold the online recursion at the requested round.  The goal becomes
  -- exactly the adversary's promised range condition.
  rw [episodeLossNat.eq_1]
  exact adversary.valid t.val
    (fun s : Fin t.val => episodeLossNat learner adversary s.val)
    (learner.weights t.val (fun s : Fin t.val => episodeLossNat learner adversary s.val))
    i

/-- The loss sequence stored by an `Episode` is valid (all losses in `[0,1]`): rewrite the
stored sequence to the generated one and use `episodeLossSeq_valid`. -/
theorem Episode.losses_valid {N T : ℕ} [NeZero N] (episode : Episode N T) :
    episode.losses.Valid := by
  rw [episode.losses_eq_generated]
  exact episodeLossSeq_valid episode.learner episode.adversary

/-! ## Hedge Regret Against Adaptive Adversaries -/

/-- **Hedge against an adaptive adversary**: for any learning rate `η > 0` and any adaptive
adversary, the regret of Hedge on the loss sequence generated by playing `hedgePolicy N η`
against that adversary over `T` rounds is at most `(ln N)/η + ηT/8` [CBL06, Thm 2.2] (in the
nonoblivious setting of [CBL06, §4.1]).  Deviation: adaptivity is handled by the pathwise
reduction — `hedge_regret_bound_tight` already holds for every fixed valid loss sequence, so
once the interaction has generated such a sequence no separate argument is needed; in
particular no randomization of the learner is modeled. -/
theorem hedge_regret_bound_tight_episode {N T : ℕ} [NeZero N] (η : ℝ)
    (hη_pos : 0 < η) (adversary : AdaptiveAdversary N) :
    regret η (episodeLossSeq T (hedgePolicy N η) adversary)
      ≤ Real.log N / η + η * T / 8 := by
  -- The reduction is deliberately small: generated episodes are valid loss
  -- sequences, and `hedge_regret_bound_tight` already handles every such
  -- sequence pathwise.
  exact hedge_regret_bound_tight η hη_pos
    (episodeLossSeq T (hedgePolicy N η) adversary)
    (episodeLossSeq_valid (hedgePolicy N η) adversary)

/-- **Hedge against an adaptive adversary**, packaged form: for any `η > 0` and any episode
over `T` rounds whose learner is `hedgePolicy N η`, the regret of Hedge on the episode's
realized loss sequence is at most `(ln N)/η + ηT/8` [CBL06, Thm 2.2].  This is
`hedge_regret_bound_tight_episode` after rewriting the stored losses as the generated ones. -/
theorem hedge_regret_bound_tight_of_episode {N T : ℕ} [NeZero N] (η : ℝ)
    (hη_pos : 0 < η) (episode : Episode N T)
    (hlearner : episode.learner = hedgePolicy N η) :
    regret η episode.losses ≤ Real.log N / η + η * T / 8 := by
  rw [episode.losses_eq_generated, hlearner]
  exact hedge_regret_bound_tight_episode η hη_pos episode.adversary
