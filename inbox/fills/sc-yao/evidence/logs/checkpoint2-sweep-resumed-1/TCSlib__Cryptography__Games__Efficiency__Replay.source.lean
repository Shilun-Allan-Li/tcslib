/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Machines

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Replaying a computation with a next-move function (efficiency fill, S3)

A next-move function `f` (of the log so far) **replays** an oracle computation `t` when `f []` is
`t`'s first move and, at a query, `f` extended by the query and any answer replays the
continuation (`ReplaysFrom`). If it does and `t` makes at most `b` queries, then `buildComp` of `f`
with budget `b` is `t` itself (`buildComp_of_replaysFrom`): the budget never cuts the replay
short. The interactive efficiency target (`Games.exists_interactiveHandlerMachine`) uses it, with
the cost scaling lemma `costBoundedBy_mul` (route note
`briefs/pass-shelat-ch5-8/design/S2b-efficiency.md`, §"Shared pieces", S3, and §"T2", step 4).

## Main definitions

* `EffFill.ReplaysFrom t f`: the next-move function `f` replays `t`.

## Main results

* `EffFill.buildComp_of_replaysFrom`: a replay within budget builds the computation.
* `EffFill.costBoundedBy_mul`: charging `p` per query multiplies a query bound by `p`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §3.8.1 (oracle machines).
-/

namespace TCSlib.Cryptography.Games.EffFill

variable {ι α : Type} {spec : OracleSpec ι}

/-- **`f` replays `t`:** at a return `a`, `f []` is the output `a`; at a query `x` to oracle `i`
with continuation `k`, `f []` is that query and, for every answer `y`, the function
`O ↦ f (⟨i, x, y⟩ :: O)` replays `k y`. (The argument of `f` is the log after the current
position.) -/
def ReplaysFrom : OracleComp spec α → (QueryLog spec → Move spec α) → Prop
  | .pure a, f => f [] = .ret a
  | .query i x k, f => f [] = .query i x ∧ ∀ y, ReplaysFrom (k y) fun O => f (⟨i, x, y⟩ :: O)

/-- A return is replayed when the function outputs it: `ReplaysFrom (pure a) f ↔ f [] = ret a`. -/
theorem replaysFrom_pure_iff (a : α) (f : QueryLog spec → Move spec α) :
    ReplaysFrom (.pure a) f ↔ f [] = .ret a :=
  Iff.rfl

/-- A query is replayed when the function asks it and replays every continuation:
`ReplaysFrom (query i x k) f ↔ f [] = query i x ∧ ∀ y, ReplaysFrom (k y) (f ∘ (⟨i, x, y⟩ :: ·))`. -/
theorem replaysFrom_query_iff (i : ι) (x : spec.dom i) (k : spec.rng i → OracleComp spec α)
    (f : QueryLog spec → Move spec α) :
    ReplaysFrom (.query i x k) f ↔
      f [] = .query i x ∧ ∀ y, ReplaysFrom (k y) fun O => f (⟨i, x, y⟩ :: O) :=
  Iff.rfl

/-- **A replay within budget builds the computation.** If `O ↦ next (hist ++ O)` replays `t` and
`t` makes at most `b` queries, then `buildComp next timeout b hist = t`.

**Proof sketch.** Induction on `t`, generalizing the log and the budget. A return `a` is
`next hist = ret a`, and `buildComp` returns `a` at every budget (`buildComp_zero_of_ret`,
`buildComp_succ_of_ret`). A query costs `1 ≤ b`, so `b = b' + 1`, and `buildComp` asks the same
query (`buildComp_succ_of_query`); each continuation is replayed from `hist ++ [⟨i, x, y⟩]`
(`List.append_assoc`) within `b'`, and agrees by induction. -/
theorem buildComp_of_replaysFrom (next : QueryLog spec → Move spec α) (timeout : α) :
    ∀ (t : OracleComp spec α) (hist : QueryLog spec) (b : ℕ),
      ReplaysFrom t (fun O => next (hist ++ O)) → t.CostBoundedBy (fun _ => 1) b →
        buildComp next timeout b hist = t := by
  intro t
  induction t with
  | pure a =>
    intro hist b h _
    have h' : next hist = .ret a := by
      have := (replaysFrom_pure_iff a _).1 h
      rwa [List.append_nil] at this
    cases b with
    | zero => exact buildComp_zero_of_ret h'
    | succ b => exact buildComp_succ_of_ret h'
  | query i x k ih =>
    intro hist b h hc
    obtain ⟨h1, h2⟩ := (replaysFrom_query_iff i x k _).1 h
    rw [List.append_nil] at h1
    obtain ⟨hb, hk⟩ := (OracleComp.costBoundedBy_query _ i x k b).1 hc
    obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    rw [buildComp_succ_of_query h1]
    refine congrArg (OracleComp.query i x) (funext fun y => ih y _ b ?_ ?_)
    · have e : (fun O => next ((hist ++ [⟨i, x, y⟩]) ++ O)) =
          fun O => next (hist ++ ⟨i, x, y⟩ :: O) := by
        funext O
        rw [List.append_assoc, List.singleton_append]
      rw [e]
      exact h2 y
    · have := hk y
      rwa [Nat.add_sub_cancel] at this

/-- **Charging `p` per query multiplies the bound by `p`:** a computation with at most `q` queries
is cost-bounded by `q · p` when every query costs `p`.

**Proof sketch.** Induction on the computation: a query needs `1 ≤ q`, so `p ≤ q · p`, and the
continuation's bound `(q − 1) · p` is `q · p − p` (`Nat.sub_one_mul`). -/
theorem costBoundedBy_mul {c : OracleComp spec α} {q : ℕ}
    (h : c.CostBoundedBy (fun _ => 1) q) (p : ℕ) : c.CostBoundedBy (fun _ => p) (q * p) := by
  induction c generalizing q with
  | pure a => exact OracleComp.costBoundedBy_pure _ _ _
  | query i x k ih =>
    obtain ⟨hq, hk⟩ := (OracleComp.costBoundedBy_query _ i x k q).1 h
    refine (OracleComp.costBoundedBy_query _ i x k _).2 ⟨?_, fun y => ?_⟩
    · exact Nat.le_mul_of_pos_left p hq
    · rw [← Nat.sub_one_mul]
      exact ih y (hk y)

end TCSlib.Cryptography.Games.EffFill
