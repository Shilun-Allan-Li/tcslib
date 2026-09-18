/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Finite
import TCSlib.Complexity.TuringMachine.Robustness.ObliviousSchedule

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Snapshots and locality of oblivious computation

[AB09, §2.3.4, pp. 47-49]: the *snapshot* of a machine's execution at step `i`
is the constant-size record of its state and the symbols under its heads, and
— for an **oblivious** machine — the snapshot at step `i` is determined by the
snapshot at step `i - 1`, the snapshots at the *last-visit* times of the
current work-tape cells, and the input symbol at the (input-independent)
current input position. "Computation is local" is this determination, and it
is the entire mathematical content behind the Cook-Levin tableau: everything
else is formula bookkeeping and machine construction. This module defines
snapshots, the input-length-indexed schedule of an oblivious machine, the
last-visit function, the finite reconstruction functions, and states the
determination theorems.

## Design and deviations from [AB09]

* **Multi-tape, not two-tape**: [AB09] proves Lemma 2.11 for two-tape
  oblivious machines and notes (footnote 5) that the proof generalizes to any
  oblivious machine; our supply side `Complexity.oblivious_of_mem_DTIME` is
  quadratic with unrestricted tape count, so the snapshot carries one read
  symbol per work tape (`k + 1` symbols plus the state) and there is one
  last-visit function per work tape. The snapshot size is still a constant of
  the machine.
* **The schedule is defined from the all-`false` reference input**:
  `Turing.FinTM.Oblivious` says head positions agree across equal-length
  inputs, so running on `List.replicate n false` *defines* the position
  functions ([AB09], p. 47: "run it on the trivial input"), and
  `Complexity.oblivious_schedule_eq` transports them to every input of length
  `n`. This is also exactly how the emitting machine will *compute* the
  schedule (the clocked-simulation obligation of the hardness sketch).
* **First visits read blank, not [AB09]'s `prev(i) = 1` convention**
  ([AB09], footnote 6): our `Complexity.prevVisit` returns `none` when the
  current cell was never visited before, and the determination theorem
  returns the blank symbol there — work tapes start blank, so this is the
  content, with no arbitrary time-`1` reference. **Seeded design question (b)
  for the phase-4 audit.**
* **Obliviousness constrains positions only**: unlike [AB09]'s convention
  ("`M`'s computation takes the same time for all inputs of size `n`"), our
  `Turing.FinTM.Oblivious` does not force equal halting times across
  equal-length inputs. Snapshots remain well-defined past halting (halting is
  absorbing), and every reconstruction function below carries a halted branch
  that fixes the snapshot — so the determination theorems hold at every time,
  and the tableau can run to the common *budget* rather than a common halting
  time. **Seeded design question (c) for the phase-4 audit.**
* Emissions are part of the locality story too: our machines signal through
  the append-only output tape, so the per-step emission is a function of the
  snapshot (`Complexity.emitted`), which is what lets the hardness argument
  render acceptance as a local clause family (see
  `TCSlib.Complexity.CookLevin.Hardness`).

## Main definitions

* `Complexity.Snapshot`, `Complexity.snapshotAt` — the state and the read
  symbols at a step. [AB09, §2.3.4, Figure 2.2]
* `Complexity.inputPosAt`, `Complexity.workPosAt` — the schedule, off the
  reference input. [AB09, p. 47]
* `Complexity.prevVisit` — the last previous time the work head sat on its
  current cell. [AB09, p. 48, `prev(i)`]
* `Complexity.stepState`, `Complexity.writtenOrKept`, `Complexity.emitted`,
  `Complexity.inputBitAt` — the finite reconstruction functions (the
  ingredients of [AB09]'s function `F`, eq. (2.3)).

## Main results

* `Complexity.oblivious_schedule_eq` — positions on any input equal the
  schedule. [AB09, p. 47]
* `Complexity.snapshotAt_zero` — the initial snapshot. [AB09, condition 2]
* `Complexity.snapshotAt_state_succ` — the state component steps by
  `stepState` (any machine).
* `Complexity.snapshotAt_inputSymbol` — the input component reads the input
  at the scheduled position. [AB09, `y_inputpos(i)`]
* `Complexity.snapshotAt_workSymbol` — **computation is local**: the work
  component is the last visit's written-or-kept symbol, blank on first
  visits. [AB09, eq. (2.3) and footnote 6]

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§2.3.4, pp. 46-49, Figures 2.2-2.3,
  eq. (2.3), footnotes 5-6.)
-/

namespace Complexity

open Turing

/-- The **snapshot** record [AB09, §2.3.4, Figure 2.2]: the (optional, `none`
when halted) state together with the symbol under the input head and the
symbols under the `k` work-tape heads. For a fixed machine this is a
constant-size record — `|State| + 1` states and three values per symbol — and
encodes as a constant number of bits. -/
abbrev Snapshot (M : FinTM Bool) : Type :=
  Option M.State × Option Bool × (Fin M.k → Option Bool)

/-- The snapshot of `M`'s run on `x` at time `t`: state and read symbols of
the configuration reached after `t` steps. Well-defined at every `t`
(halting is absorbing). -/
def snapshotAt (M : FinTM Bool) (x : List Bool) (t : ℕ) : Snapshot M :=
  ⟨(M.tm.runFrom (M.tm.initCfg x) t).state,
   (M.tm.runFrom (M.tm.initCfg x) t).inputSymbol,
   (M.tm.runFrom (M.tm.initCfg x) t).workTapeSymbols⟩

/-- The input-head schedule of `M` on inputs of length `n`: the (shifted)
input position at time `t` of the run on the reference input
`List.replicate n false`. For an oblivious `M` this is the position on
*every* length-`n` input (`Complexity.oblivious_schedule_eq`); [AB09]'s
`inputpos(i)`, defined by running on the trivial input (p. 47). -/
def inputPosAt (M : FinTM Bool) (n t : ℕ) : ℕ :=
  ((M.tm.runFrom (M.tm.initCfg (List.replicate n false)) t).inputPos : ℕ)

/-- The work-head schedule of `M` on inputs of length `n`: tape `τ`'s head
position at time `t` on the reference input. -/
def workPosAt (M : FinTM Bool) (n t : ℕ) (τ : Fin M.k) : ℤ :=
  (M.tm.runFrom (M.tm.initCfg (List.replicate n false)) t).workTapePos τ

/-- [AB09]'s `prev` (p. 48): the **last** time before `t` at which tape `τ`'s
head (on length-`n` inputs) sat on its time-`t` cell — `none` when the cell
was never visited before `t` (deviating from [AB09]'s footnote-6 convention
`prev(i) = 1`; first visits read blank, see the deviations list). -/
def prevVisit (M : FinTM Bool) (n t : ℕ) (τ : Fin M.k) : Option ℕ :=
  ((List.range t).filter fun s => workPosAt M n s τ == workPosAt M n t τ).max?

/-- The state after one step, as a function of the snapshot alone: halted
stays halted, and a live state applies the transition selected by the read
symbols. One ingredient of [AB09]'s function `F` (eq. (2.3)). -/
def stepState (M : FinTM Bool) (s : Snapshot M) : Option M.State :=
  match s.1 with
  | none => none
  | some q => (M.tm.tr q s.2.1 s.2.2).state

/-- The symbol a step leaves in the cell under work head `τ`, as a function
of the snapshot: a halted step keeps the read symbol; a live step writes the
transition's symbol, or keeps the read symbol when the transition writes
nothing (the model's optional write). The second ingredient of `F`: the
content of a cell after its last visit. -/
def writtenOrKept (M : FinTM Bool) (s : Snapshot M) (τ : Fin M.k) : Option Bool :=
  match s.1 with
  | none => s.2.2 τ
  | some q => ((M.tm.tr q s.2.1 s.2.2).workTapes τ).1.getD (s.2.2 τ)

/-- The symbol a step emits onto the append-only output tape, as a function
of the snapshot: `none` when halted or when the transition emits nothing.
This is what makes acceptance-by-output a *local* condition (see
`TCSlib.Complexity.CookLevin.Hardness`). -/
def emitted (M : FinTM Bool) (s : Snapshot M) : Option Bool :=
  match s.1 with
  | none => none
  | some q => (M.tm.tr q s.2.1 s.2.2).output

/-- The boundary-aware input read: position `0` and positions beyond the
input read blank; interior position `p` reads bit `p - 1`. Matches
`Turing.Cfg.inputSymbol` at every reachable position. -/
def inputBitAt (x : List Bool) (p : ℕ) : Option Bool :=
  if p = 0 then none else x[p - 1]?

/-- **The schedule is input-independent** [AB09, p. 47]: on an oblivious
machine, the head positions of the run on any `x` agree at every time with
the reference-input schedule of length `|x|`.

**Proof sketch.** Instantiate `Turing.FinTM.Oblivious` at `x` and
`List.replicate x.length false` (`List.length_replicate` equalizes the
lengths); the two conjuncts are the two claims. -/
theorem oblivious_schedule_eq {M : FinTM Bool} (hM : M.Oblivious)
    (x : List Bool) (t : ℕ) :
    ((M.tm.runFrom (M.tm.initCfg x) t).inputPos : ℕ) = inputPosAt M x.length t ∧
    (M.tm.runFrom (M.tm.initCfg x) t).workTapePos = workPosAt M x.length t := by
  sorry

/-- **The initial snapshot** [AB09, condition 2, adapted to our
initialization]: at time `0` the machine is in its initial state, the input
head (at position `1`) reads the first input bit — blank on the empty
input — and every work tape reads blank.

**Proof sketch.** `Turing.MultiTapeTM.runFrom_zero` reduces to `Turing.Cfg.init`:
state `some q₀`; `Turing.Cfg.inputSymbol` at position `1` is `x[0]` for
nonempty `x` and the boundary blank for `x = []`, which is `inputBitAt x 1` in
both cases; the initial work tapes are the constant-`none` function, so every
work read is blank. -/
theorem snapshotAt_zero (M : FinTM Bool) (x : List Bool) :
    snapshotAt M x 0 = ⟨some M.tm.q₀, inputBitAt x 1, fun _ => none⟩ := by
  sorry

/-- **The state component is locally determined** (any machine, oblivious or
not): the state at time `t + 1` is `stepState` of the snapshot at time `t`.

**Proof sketch.** `Turing.MultiTapeTM.runFrom_succ_eq_step'` and the
definition of `Turing.MultiTapeTM.step`: halted configurations are fixed
(matching `stepState`'s halted branch), and a live step applies the action
selected by exactly the state and read symbols — the snapshot's data — whose
`Turing.Action.apply` sets the successor state to the action's state field. -/
theorem snapshotAt_state_succ (M : FinTM Bool) (x : List Bool) (t : ℕ) :
    (snapshotAt M x (t + 1)).1 = stepState M (snapshotAt M x t) := by
  sorry

/-- **The input component reads the scheduled position** [AB09, the
`y_inputpos(i)` wiring]: on an oblivious machine, the input symbol of the
time-`t` snapshot on `x` is the input bit at the schedule's position.

**Proof sketch.** `Turing.Cfg.inputSymbol` reads blank at the two boundary
positions and bit `p - 1` at interior `p`, which is `inputBitAt x p` for
every position `p ≤ |x| + 1`; positions are always in that range
(`Fin (|x| + 2)`). Rewrite `p` to the schedule by
`Complexity.oblivious_schedule_eq`. -/
theorem snapshotAt_inputSymbol {M : FinTM Bool} (hM : M.Oblivious)
    (x : List Bool) (t : ℕ) :
    (snapshotAt M x t).2.1 = inputBitAt x (inputPosAt M x.length t) := by
  sorry

/-- **Computation is local** [AB09, eq. (2.3) with footnote 6]: on an
oblivious machine, the symbol read by work head `τ` at time `t` is the
written-or-kept symbol of the snapshot at the cell's last visit, and blank
when the cell was never visited before — the contents of the current cell
have not been touched between `prevVisit` and `t`.

**Proof sketch.** Let `p = workPosAt |x| t τ`, the time-`t` position on `x`
by `Complexity.oblivious_schedule_eq`. The cell's content changes only at
steps whose head position is `p`: `Turing.Action.apply` updates tape `τ` at
the head position only (`Function.update`), and a step that writes nothing —
or a halted step — leaves the content equal to the symbol under the head,
which is what `Complexity.writtenOrKept` returns in those branches. If
`prevVisit = some s`, then `s` is the greatest earlier visit
(`List.max?` membership/maximality over the filtered range): induct from
`s + 1` to `t` — no intermediate step visits `p`, so the content at `p` is
constant on that interval and equals the written-or-kept symbol of the
time-`s` snapshot; the read at `t` is that content. If `prevVisit = none`,
no earlier step visited `p`; the initial work tapes are blank and unvisited
cells stay blank, so the read is `none`. Halting needs no separate case: a
halted run's positions are frozen, so later times' `prevVisit` chains
terminate at the same cell values (`writtenOrKept`'s halted branch is the
identity on the read). -/
theorem snapshotAt_workSymbol {M : FinTM Bool} (hM : M.Oblivious)
    (x : List Bool) (t : ℕ) (τ : Fin M.k) :
    (snapshotAt M x t).2.2 τ =
      match prevVisit M x.length t τ with
      | none => none
      | some s => writtenOrKept M (snapshotAt M x s) τ := by
  sorry

end Complexity
