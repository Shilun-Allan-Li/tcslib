/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.OracleNondeterministic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Oracle locality: runs under agreeing oracles coincide

The locality layer of the relativization theorem ([AB09, Theorem 3.7]; [BGS75,
§3]): an oracle machine's `t`-step run from the initial configuration consults
the oracle only on the strings it actually submits, each of length less than
the elapsed time. Hence two oracles that agree on every submitted string — or,
more coarsely, on every string of length below the horizon — produce literally
the same run. This is what lets the Baker-Gill-Solovay stage construction run a
machine against a *partial* oracle (undetermined queries answered "no") and
transfer the verdict to the completed oracle, provided the completion never
touches a queried string.

## Design

* `Turing.OracleTM.queriesWithin M O x t` records the query strings submitted
  during the first `t` steps of the initialized run: one entry for each step
  index `s < t` at which the machine sits in `qQuery` (that step submits the
  current query-tape contents). It is a *list* (with multiplicity, in step
  order), so the stage construction's counting argument — at most `t` queries
  in `t` steps — is its length bound, with no finiteness side conditions.
* The nondeterministic variant `Turing.OracleNDTM.queriesAlong N O x w` runs
  along a fixed choice word `w`, mirroring `Turing.OracleNDTM.runWith`; its
  horizon is `w.length` (the first `t` steps along `w` are the queries along
  `w.take t`).
* The query-set form (`runFrom_eq_of_agree_queriesWithin`) is deliberately
  asymmetric: the query list is computed along the run under the *first*
  oracle, which is exactly the shape the stage construction consumes (run with
  the partial oracle, then extend it).

## Main definitions

* `Turing.OracleTM.queriesWithin` — the query strings submitted in the first
  `t` steps of a deterministic initialized oracle run.
* `Turing.OracleNDTM.queriesAlong` — the query strings submitted along a fixed
  choice word of a nondeterministic initialized oracle run.

## Main results (all sorried; phase-P3.2 statements)

* `Turing.OracleTM.runFrom_eq_of_agree_length_lt` — agreement on all strings of
  length `< t` makes the `t`-step runs coincide.
* `Turing.OracleTM.runFrom_eq_of_agree_queriesWithin` — agreement on the
  submitted queries alone makes the `t`-step runs coincide.
* `Turing.OracleNDTM.runWith_eq_of_agree_length_lt`,
  `Turing.OracleNDTM.runWith_eq_of_agree_queriesAlong` — the same two along a
  fixed choice word.
* `Turing.OracleTM.length_le_of_mem_queriesWithin`,
  `Turing.OracleNDTM.length_le_of_mem_queriesAlong` — every submitted query is
  short (length at most the horizon).
* `Turing.OracleTM.queriesWithin_length_le` — at most `t` queries in `t` steps
  (the stage construction's counting bound).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§3.4, proof of Theorem 3.7.)
* [BGS75] T. Baker, J. Gill, R. Solovay, *Relativizations of the P =? NP
  question*, SIAM Journal on Computing 4(4), 1975. (§3: runs against finite
  partial oracles.)
-/

namespace Turing

variable {k : ℕ} {Symbol State : Type*}

namespace OracleTM

open Classical in
/-- The query strings submitted by the oracle machine `M`, with oracle `O`, on
input `x`, during the first `t` steps of the initialized run: one entry per step
index `s < t` at which the run sits in the query state (that step submits the
current contents of the query tape, `Turing.OracleTM.queryString`), in step
order and with multiplicity. [AB09, proof of Theorem 3.7: "the strings queried
by `M_i` on input `1^n`"] -/
noncomputable def queriesWithin (M : OracleTM k Symbol State) (O : Language Symbol)
    (x : List Symbol) (t : ℕ) : List (List Symbol) :=
  (List.range t).filterMap fun s =>
    if (M.runFrom O (M.initCfg x) s).state = some M.qQuery then
      some (queryString (M.runFrom O (M.initCfg x) s))
    else none

/-- **Length-locality of deterministic oracle runs**: if two oracles agree on
every string of length less than `t`, the `t`-step initialized runs under them
coincide — a `t`-step run can only ever submit queries of length below `t`.
[AB09, proof of Theorem 3.7; BGS75, §3]

**Proof sketch.** Strengthen to: for every `s ≤ t` the two runs coincide at
horizon `s`, by induction on `s`. The configurations after `s` steps agree by
the inductive hypothesis; for the next step, either the common configuration is
not in the query state — then `Turing.OracleTM.step_eq_of_ne_qQuery` makes the
step oracle-independent — or it is, and the submitted string is the common
configuration's `Turing.OracleTM.queryString`, of length at most `s < t` by
`Turing.OracleTM.queryString_length_le`, on which `O` and `O'` agree, so both
steps move to the same answer state. Fill obligations: the `≤ t`-indexed
induction (successor unfolding `Function.iterate_succ_apply'` of
`Turing.OracleTM.runFrom`), and the two-case analysis of
`Turing.OracleTM.step` at a common configuration. -/
theorem runFrom_eq_of_agree_length_lt (M : OracleTM k Symbol State)
    (O O' : Language Symbol) (x : List Symbol) (t : ℕ)
    (h : ∀ z : List Symbol, z.length < t → (z ∈ O ↔ z ∈ O')) :
    M.runFrom O (M.initCfg x) t = M.runFrom O' (M.initCfg x) t := by
  sorry

/-- **Query-set locality of deterministic oracle runs** — the form the
Baker-Gill-Solovay stage construction consumes: if two oracles agree on every
string the run with the *first* oracle actually submits in its first `t` steps,
the `t`-step initialized runs coincide. In the stage construction `O` is the
finite partial oracle (undetermined strings answered "no") and `O'` the
completed oracle, which by construction never disturbs a queried string.
[AB09, proof of Theorem 3.7; BGS75, §3]

**Proof sketch.** As in `Turing.OracleTM.runFrom_eq_of_agree_length_lt`,
by induction on `s ≤ t` with the runs kept equal: at a non-query step
`Turing.OracleTM.step_eq_of_ne_qQuery` applies; at a query step the submitted
string is, by definition of `Turing.OracleTM.queriesWithin` (its step index
`s` lies in `List.range t` and the state condition holds along the `O`-run,
which the inductive hypothesis identifies with the `O'`-run), an element of
`M.queriesWithin O x t`, where `h` makes both oracles answer alike. Fill
obligations: the `List.mem_filterMap` membership introduction, and the same
run-equality induction as the length-locality lemma. -/
theorem runFrom_eq_of_agree_queriesWithin (M : OracleTM k Symbol State)
    (O O' : Language Symbol) (x : List Symbol) (t : ℕ)
    (h : ∀ z ∈ M.queriesWithin O x t, (z ∈ O ↔ z ∈ O')) :
    M.runFrom O (M.initCfg x) t = M.runFrom O' (M.initCfg x) t := by
  sorry

/-- **Submitted queries are short**: every string in `queriesWithin M O x t`
has length at most `t`. (Sharper: a query submitted at step `s < t` has length
at most `s`.) [AB09, proof of Theorem 3.7, the length bookkeeping]

**Proof sketch.** A member of the `List.filterMap` arises from some `s ∈
List.range t` with the run in the query state after `s` steps, and equals
`Turing.OracleTM.queryString` of that configuration;
`Turing.OracleTM.queryString_length_le` bounds its length by `s ≤ t`. -/
theorem length_le_of_mem_queriesWithin {M : OracleTM k Symbol State}
    {O : Language Symbol} {x : List Symbol} {t : ℕ} {z : List Symbol}
    (hz : z ∈ M.queriesWithin O x t) : z.length ≤ t := by
  sorry

/-- **At most `t` queries in `t` steps**: the query list of a `t`-step run has
length at most `t` — the counting half of the stage construction (a
polynomial-time run cannot touch all `2^n` strings of length `n`).
[AB09, proof of Theorem 3.7, the counting argument; BGS75, §3]

**Proof sketch.** `Turing.OracleTM.queriesWithin` is a `List.filterMap` over
`List.range t`: `List.length_filterMap_le` and `List.length_range`. -/
theorem queriesWithin_length_le (M : OracleTM k Symbol State)
    (O : Language Symbol) (x : List Symbol) (t : ℕ) :
    (M.queriesWithin O x t).length ≤ t := by
  sorry

end OracleTM

namespace OracleNDTM

open Classical in
/-- The query strings submitted by the nondeterministic oracle machine `N`,
with oracle `O`, on input `x`, along the choice word `w`: one entry per step
index `s < w.length` at which the branch (the run under `w.take s`) sits in the
query state, in step order and with multiplicity — the
`Turing.OracleNDTM.runWith` analogue of `Turing.OracleTM.queriesWithin`. The
queries of the first `t` steps along `w` are the queries along `w.take t`.
[AB09, proof of Theorem 3.7, applied branchwise] -/
noncomputable def queriesAlong (N : OracleNDTM k Symbol State) (O : Language Symbol)
    (x : List Symbol) (w : List Bool) : List (List Symbol) :=
  (List.range w.length).filterMap fun s =>
    if (N.runWith O (w.take s) (N.initCfg x)).state = some N.qQuery then
      some (OracleTM.queryString (N.runWith O (w.take s) (N.initCfg x)))
    else none

/-- **Length-locality of nondeterministic oracle runs, branchwise**: if two
oracles agree on every string of length less than `w.length`, the runs along
the fixed choice word `w` coincide. [AB09, proof of Theorem 3.7; Definition
3.4, "nondeterministic oracle TMs are defined similarly"]

**Proof sketch.** Induction on `s ≤ w.length` with the branch prefixes kept
equal (`Turing.OracleNDTM.runWith_cons` unfolds one consumed choice bit). A
`Turing.OracleNDTM.stepWith` from a common configuration under the common
choice bit is oracle-independent away from `qQuery` (the transition-table
branch does not mention the oracle; halted configurations are fixed by
`Turing.OracleNDTM.stepWith_of_halt`), and at `qQuery` both oracles resolve the
common query string alike, its length being below `w.length` by the
nondeterministic query-length bound (the invariant behind
`Turing.OracleNDTM.length_le_of_mem_queriesAlong` below, at horizon `s`). Fill
obligations: an `OracleNDTM.stepWith` analogue of
`Turing.OracleTM.step_eq_of_ne_qQuery`, and the `w.take`-indexed induction
(`List.take_succ` against `Turing.OracleNDTM.runWith_append`). -/
theorem runWith_eq_of_agree_length_lt (N : OracleNDTM k Symbol State)
    (O O' : Language Symbol) (x : List Symbol) (w : List Bool)
    (h : ∀ z : List Symbol, z.length < w.length → (z ∈ O ↔ z ∈ O')) :
    N.runWith O w (N.initCfg x) = N.runWith O' w (N.initCfg x) := by
  sorry

/-- **Query-set locality of nondeterministic oracle runs, branchwise**: if two
oracles agree on every string the branch under the *first* oracle actually
submits along `w`, the runs along `w` coincide.
[AB09, proof of Theorem 3.7; BGS75, §3]

**Proof sketch.** The same induction on `s ≤ w.length` as
`Turing.OracleNDTM.runWith_eq_of_agree_length_lt`, with the query-step case
discharged by membership of the submitted string in
`N.queriesAlong O x w` (its index lies in `List.range w.length` and the state
condition holds along the `O`-branch, which the inductive hypothesis identifies
with the `O'`-branch) and the agreement hypothesis `h` — mirroring the
deterministic `Turing.OracleTM.runFrom_eq_of_agree_queriesWithin`. -/
theorem runWith_eq_of_agree_queriesAlong (N : OracleNDTM k Symbol State)
    (O O' : Language Symbol) (x : List Symbol) (w : List Bool)
    (h : ∀ z ∈ N.queriesAlong O x w, (z ∈ O ↔ z ∈ O')) :
    N.runWith O w (N.initCfg x) = N.runWith O' w (N.initCfg x) := by
  sorry

/-- **Submitted queries are short, branchwise**: every string in
`queriesAlong N O x w` has length at most `w.length`.
[AB09, proof of Theorem 3.7, the length bookkeeping]

**Proof sketch.** The member arises at some step index `s < w.length`, as
`Turing.OracleTM.queryString` of the branch configuration after `s` steps. The
deterministic bound `Turing.OracleTM.queryString_length_le` rests on the
head-position/blank-cell invariant of initialized runs, which transfers
verbatim to `Turing.OracleNDTM.runWith`: a `stepWith` either applies a
transition-table action (writes only at the old head position, moves heads by
at most one — the same `Turing.Action.apply` facts), resolves a query (tapes
and heads unchanged), or is halted (identity). Fill obligations: the
nondeterministic run invariant (the `runWith` analogue of the private
`runFrom_workTapes_invariant` of `TCSlib.Complexity.TuringMachine.Oracle` —
its natural home is the frozen `Oracle`/`OracleNondeterministic` pair, so it
lands here; flagged for promotion), then the `Nat.find` bound exactly as in
`Turing.OracleTM.queryString_length_le`. -/
theorem length_le_of_mem_queriesAlong {N : OracleNDTM k Symbol State}
    {O : Language Symbol} {x : List Symbol} {w : List Bool} {z : List Symbol}
    (hz : z ∈ N.queriesAlong O x w) : z.length ≤ w.length := by
  sorry

end OracleNDTM

end Turing
