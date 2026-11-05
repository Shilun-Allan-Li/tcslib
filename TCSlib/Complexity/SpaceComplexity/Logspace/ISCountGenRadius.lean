/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Logspace.ISCountMath
import TCSlib.Complexity.SpaceComplexity.ExpBFS.Radius

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Balls of the configuration graph and reachable codes

The window-growing counting machine `Complexity.LogProg.ISGen.igA` [AB09, §4.3.2] computes,
at the window radius `s`, the balls `C_j` (`Complexity.LogProg.ISCount.ball`) of the
configuration graph of a decider `N` over the codes below a bound `K` at least the code bound
`2 ^ (codeK N · (s + logSpace |x| + 1))`. This file identifies its largest ball `C_K` with
the reachable codes `Complexity.ExpBFS.rset N x s` of
`TCSlib.Complexity.SpaceComplexity.ExpBFS.Radius` (`mem_ball_iff_rcode`,
`card_ball_eq_rset`), so that the radius-growing facts proved there apply to the counts the
machine computes, and records the two acceptance facts the radius loop uses
(`mem_of_exists_acc`, `mem_iff_exists_acc_of_card_eq`). The first is
`Complexity.Codec.mem_of_codePath`; the second is the radius-`s` form of
`Complexity.ExpBFS.mem_iff_of_card_eq` (which, from equal counts at `s - 1` and `s`,
concludes at radius `s - 1`; codes depend on the radius, so the form used by the loop is
re-derived from `Complexity.ExpBFS.winRun_of_card_eq`).

Configuration-graph infrastructure for [AB09, §4.3.2]; not itself a result of the book.

## Main definitions

* `Complexity.LogProg.ISGen.InitM`, `Complexity.LogProg.ISGen.AccM` — the initial-code and
  accepting-code predicates at radius `s`, as memberships in the code languages.

## Main results

* `Complexity.LogProg.ISGen.mem_ball_iff_rcode`, `Complexity.LogProg.ISGen.card_ball_eq_rset`
  — the largest ball is the set of reachable codes.
* `Complexity.LogProg.ISGen.card_ball_zero_code` — the ball `C_0` is the initial code.
* `Complexity.LogProg.ISGen.noAcc_balls_iff` — no accepting code in the balls iff none is
  reachable.
* `Complexity.LogProg.ISGen.mem_of_exists_acc`,
  `Complexity.LogProg.ISGen.mem_iff_exists_acc_of_card_eq` — an accepting reachable code
  gives membership; once the counts at `s - 1` and `s` agree, membership is an accepting
  reachable code at radius `s`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.1, §4.3.2.)
-/

namespace Complexity.LogProg

namespace ISGen

open Turing Codec ExpBFS ISCount

variable {N : FinNDTM Bool} {x : List Bool}

/-- The initial-code predicate at radius `s`, as a membership. -/
abbrev InitM (N : FinNDTM Bool) (x : List Bool) (s : ℕ) (u : ℕ) : Prop :=
  pairEncode x (pairEncode (Nat.bits u) (Nat.bits s)) ∈ initLang N

/-- The accepting-code predicate at radius `s`, as a membership. -/
abbrev AccM (N : FinNDTM Bool) (x : List Bool) (s : ℕ) (u : ℕ) : Prop :=
  pairEncode x (pairEncode (Nat.bits u) (Nat.bits s)) ∈ acceptLang N

/-- **The largest ball is the set of reachable codes**: for a code bound `K` at least
`2 ^ (codeK N · (s + logSpace |x| + 1))`, a code is in the ball `C_K` of the configuration
graph at radius `s` (codes below `K`) iff it is reachable from the initial code.

**Proof sketch.** (⇒) A walk is a path of step pairs (`walkLe_reach`). (⇐) Every code on a
path from the initial code is reachable, hence below the code bound (`rcode_lt`); the path is
then a walk through codes below `K` (`exists_walkLe`), shortened to at most `K` steps
(`walkLe_short`). -/
theorem mem_ball_iff_rcode {s K : ℕ} (hK : 2 ^ (codeK N * (s + logSpace x.length + 1)) ≤ K)
    (t : ℕ) : t ∈ ball K (StepRel N x s) (InitM N x s) K ↔ RCode N x s t := by
  rw [mem_ball]
  constructor
  · rintro ⟨u, hu, hinit, hw⟩
    rw [InitM, mem_initLang] at hinit
    subst hinit
    exact (walkLe_reach hu hw).mono fun a b hab => hab.2.2
  · intro ht
    have hpath : ∀ t, RCode N x s t → Relation.ReflTransGen
        (fun u v => u < K ∧ v < K ∧ StepRel N x s u v) (cfgCode s (N.tm.initCfg x)) t := by
      intro t ht
      induction ht with
      | refl => exact Relation.ReflTransGen.refl
      | @tail b c hab hbc ih =>
        exact ih.tail ⟨(rcode_lt hab).trans_le hK, (rcode_lt (hab.tail hbc)).trans_le hK, hbc⟩
    have h0 : cfgCode s (N.tm.initCfg x) < K := (cfgCode_lt s _).trans_le hK
    obtain ⟨j, hw⟩ := exists_walkLe (hpath t ht)
    exact ⟨_, h0, by rw [InitM, mem_initLang], walkLe_short ((rcode_lt ht).trans_le hK) h0 hw⟩

/-- **The size of the largest ball is the number of reachable codes.** -/
theorem card_ball_eq_rset {s K : ℕ} (hK : 2 ^ (codeK N * (s + logSpace x.length + 1)) ≤ K) :
    (ball K (StepRel N x s) (InitM N x s) K).card = (rset N x s).card := by
  classical
  rw [← card_filter_rcode hK]
  congr 1
  ext t
  rw [mem_ball_iff_rcode hK, Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h => ⟨(rcode_lt h).trans_le hK, h⟩, fun h => h.2⟩

/-- **The ball `C_0` is the initial code**, so it has one element. -/
theorem card_ball_zero_code {s K : ℕ} (hK : 2 ^ (codeK N * (s + logSpace x.length + 1)) ≤ K) :
    (ball K (StepRel N x s) (InitM N x s) 0).card = 1 :=
  card_ball_zero ((cfgCode_lt s (N.tm.initCfg x)).trans_le hK)
    fun u => by rw [InitM, mem_initLang]; exact eq_comm

/-- There is a reachable code (the initial one). -/
theorem one_le_card_rset (s : ℕ) : 1 ≤ (rset N x s).card :=
  Finset.card_pos.mpr ⟨_, mem_rset.mpr Relation.ReflTransGen.refl⟩

/-- **No accepting code in the balls** `C_1, …, C_K` iff no reachable code is accepting. -/
theorem noAcc_balls_iff {s K : ℕ} (hK : 2 ^ (codeK N * (s + logSpace x.length + 1)) ≤ K) :
    (∀ j, 0 < j → j ≤ K → ∀ t ∈ ball K (StepRel N x s) (InitM N x s) j, ¬ AccM N x s t) ↔
      ∀ t, RCode N x s t → ¬ AccM N x s t := by
  have hK0 : 0 < K := lt_of_lt_of_le (Nat.two_pow_pos _) hK
  constructor
  · intro h t ht
    exact h K hK0 le_rfl t ((mem_ball_iff_rcode hK t).mpr ht)
  · intro h j _ hj t ht
    exact h t ((mem_ball_iff_rcode hK t).mp (ball_mono hj ht))

/-- **An accepting reachable code makes the input a member** (at any radius). -/
theorem mem_of_exists_acc {L : Language Bool} {sp : ℕ → ℕ} (hN : N.DecidesInSpace L sp)
    {s : ℕ} (h : ∃ t, RCode N x s t ∧ AccM N x s t) : x ∈ L := by
  obtain ⟨t, ht, hacc⟩ := h
  exact mem_of_codePath hN x s _ t (by rw [mem_initLang]) ht hacc

/-- **Equal counts at `s - 1` and `s` decide membership at radius `s`**: then `x ∈ L` iff some
reachable code at radius `s` is accepting.

**Proof sketch.** (⇒) With equal counts every choice word is a window run at radius `s - 1`
(`winRun_of_card_eq`), hence at `s`; the code of an accepting branch's end is reachable and
accepting. (⇐) `mem_of_exists_acc`. -/
theorem mem_iff_exists_acc_of_card_eq {L : Language Bool} {sp : ℕ → ℕ}
    (hN : N.DecidesInSpace L sp) {s : ℕ} (hs : 1 ≤ s)
    (h : (rset N x (s - 1)).card = (rset N x s).card) :
    x ∈ L ↔ ∃ t, RCode N x s t ∧ AccM N x s t := by
  refine ⟨fun hx => ?_, mem_of_exists_acc hN⟩
  have h' : (rset N x (s - 1)).card = (rset N x (s - 1 + 1)).card := by
    rwa [Nat.sub_add_cancel hs]
  obtain ⟨T, -, -, hiff⟩ := hN x
  obtain ⟨w, -, hhalt, hout⟩ := hiff.mp hx
  have hw : WinRun N x s w := (winRun_of_card_eq h' w).mono (by omega)
  refine ⟨_, (rcode_iff s _).mpr ⟨w, hw, rfl⟩, ?_⟩
  rw [AccM, mem_acceptLang]
  exact ⟨_, hw.last, rfl, hhalt, hout⟩

end ISGen

end Complexity.LogProg
