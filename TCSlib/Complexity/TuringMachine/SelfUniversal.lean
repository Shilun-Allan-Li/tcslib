/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.UniversalStartup
import TCSlib.Complexity.TuringMachine.CodeSimulator

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The self-application universal machine `U₀`

[AB09, Exercise 4.1] at self-application: one fixed machine `U₀` that, on an input
`pairEncode α w`, simulates the machine coded by `α` on that same input and reproduces its
output, with a space overhead that is a constant factor depending on `α` only. It is the
universal machine of `Complexity.space_hierarchy`'s window route (`machine-library-design.md`
§16b item 3): a public row built from H2's step block and H5's native device, not a private host
of that proof (`policy.md` §1, *Hosts come first*).

**Status: statement gate passed 2026-10-14** (round 1, 0/0/5;
`audits/b6-hosts-statements-findings.md`). Both contracts are sorried with their proof
sketches.

## Design

* **Self-application.** The simulated input is all of `U₀`'s input, so the native device serves
  (`Turing.NativeAt`: its left boundary is a real blank) and no input position is stored or
  copied.
* **Forward only.** Halting runs within `s` cells are reproduced within `C_α · (s + 1)` cells;
  nothing is claimed of other runs, which is all the window route uses.
* **Library notions only.** The startup's endpoint is the step block's seam relation written
  out: the table on tape `1`, the unary initial state on tape `2` from cell `2`, the input head
  at `1`, the output empty. Neither statement names a declaration of the H2 promotion (H2-S);
  the prose cites its public names after the move to `Build/StepBlock.lean` (H2-M,
  `Turing.StepBlock.*`). The fill depends on H2-S round 2: the public step block contract, and
  the repaired iteration with its cofinality bound.
* **Generic in the effective scheme**; `Complexity.space_hierarchy` instantiates
  `Complexity.TimeHierarchy.code`.

## Main definitions

None: the module uses existing definitions.

## Main results

* `Turing.exists_selfStartupTM` — the startup, ending at the step block's seam (sorried).
* `Turing.exists_selfUniversal` — `U₀`, with its forward space ledger (sorried).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.4.1, Theorem 1.9: the universal machine and its step;
  Exercise 4.1: the space-bounded universal machine; §4.1.3, Theorem 4.8, whose proof the book
  assigns to Exercise 4.1. The startup and the wrapped rounds are the repository's refinement.)
-/

namespace Turing

/-- **`U₀`'s startup** (the RD-3 gate's check 2). For an effective scheme `c` there is a binary
machine with `K + 3` work tapes and an exit state such that for every code `α` there are a
time `T` and a space bound `B`, **depending on `α` only**, with the following property on every
input `pairEncode α w`. At time `T`, and not earlier, it is at its exit with:
* the input head at position `1`, `Cfg.init`'s position, and the output empty, having emitted
  nothing before (administrative output suppressed);
* tape `0`, the simulated work tape, blank, and tape `1` holding the canonical table
  `Turing.tableBitsK` of the decoded machine;
* tape `2` holding the decoded machine's initial state in unary from cell `2` (cells `0` and
  `1` blank), which is the step block's summary tape for an empty output;
* every other tape blank and every head at `0`.

Up to `T` it has visited at most `B` cells. This configuration is the step block's seam for
the decoded machine's initial configuration on the same input (H2's seam relation
`Turing.StepBlock.Rep`, `TuringMachine/Build/StepBlock.lean`, at one coded work tape). [AB09,
§1.4.1, Theorem 1.9]

**Proof sketch.** Extract and canonize: `Turing.universalCanonTM c` (buffered composition of the
prefix parser and the canonizer), with its emissions captured on a scratch tape as in
`Turing.universalCaptureTM`; it ends after `3|α| + 4 + canonizerTime |α|` steps
(`Turing.universalCanon_complete`) with `serialize (decode α)` captured and the input head at
`2|α| + 3`. The serialization is `serializeK` (`Turing.oneTapeMachineFormat.serialize_eq`):
skip its doubled state count and separator, copy the unary initial state to tape `2` at offset
`2` and the remaining table to tape `1`; clear the scratch and the buffer. Rewind the input head
to position `1` (`Turing.FinTM.timed_rewind`, `2|α| + 5` steps). Every phase depends on `α`
only, so `T` and `B` do (`Turing.MultiTapeTM.spaceUsed_le_mul_succ` at the canonizer's halting
time bounds its cells). -/
theorem exists_selfStartupTM (c : EffectiveMachineCode) :
    ∃ (K : ℕ) (P : Type) (_ : Fintype P) (_ : DecidableEq P)
      (R : MultiTapeTM (K + 3) Bool P) (exit : P),
      ∀ α : List Bool, ∃ T B : ℕ, ∀ w : List Bool,
        R.runFrom (R.initCfg (pairEncode α w)) T =
          ⟨some exit, 1,
            fun j => if j = 1 then FinTM.bufferTape (tableBitsK (c.decode α).tm.tr)
              else if j = 2 then fun p => FinTM.bufferTape (unaryFin (c.decode α).tm.q₀) (p - 2)
              else fun _ => none,
            fun _ => 0, []⟩ ∧
        (∀ u < T, (R.runFrom (R.initCfg (pairEncode α w)) u).state ≠ some exit) ∧
        (∀ u ≤ T, (R.runFrom (R.initCfg (pairEncode α w)) u).output = []) ∧
        R.spaceUsed (R.initCfg (pairEncode α w)) T ≤ B := by
  sorry

/-- **`U₀`, the self-application universal machine** (`Complexity.space_hierarchy`'s sketch;
the sibling of `Complexity.space_universal`, with the native device in place of the
bounded-prefix one). For an effective scheme `c` there is a binary machine `U₀` such that
for every code `α` there is a constant `C > 0` with: whenever the machine coded by `α` halts
on `pairEncode α w` with some output, having visited at most `s` cells, `U₀` halts on the same
input with the same output, having visited at most `C · (s + 1)` cells. Only this forward
direction is claimed; `Complexity.space_hierarchy` instantiates
`c := Complexity.TimeHierarchy.code`. [AB09, Exercise 4.1, forward clause, at self-application;
§4.1.3, Theorem 4.8]

Deviation: `C` depends on the code `α` (as in `Turing.universal`), and the input is the coded
machine's own input (self-application), so no copy and no position counter is needed.

**Proof sketch.** Startup, then wrapped rounds.
(i) *Startup.* `Turing.exists_selfStartupTM` reaches, within `B_α` cells, the step block's seam
for the coded machine's initial configuration on the same input: input head at `1`, table and
unary state in place, output empty.
(ii) *The wrapped round, with H2-S finding 4's reset invariant.* At every seam the step block's
bank represents the source configuration **with its output erased**, `{c with output := []}`
(so its summary cell is blank), while `U₀`'s own physical output is the real cumulative output
`c.output`. From such a seam at a live `c`, run H2's step block at one coded work tape, embedded
by R1 on tapes `0`–`2` (the public contract of the H2 promotion, `Turing.StepBlock.roundTM_effect`),
on `{c with output := []}`. The transition read off the table depends only on the state, the
input symbol and the work symbol, which the erasure does not change, so the round ends at the
seam of `a.apply {c with output := []}`, with summary cell
`Turing.StepBlock.summaryEmit none a.output = a.output`: the round's exact emission. A host leaf
on tape `2` then emits that bit, if any, so that `U₀`'s output becomes `(a.apply c).output`, and
blanks the cell, which re-establishes the invariant for `a.apply c`. On the halting round the
leaf runs before `U₀` halts physically (forwarding precedes the halt).
(iii) *Iteration.* Induct on the source steps, as H2-S round 2's repaired
`Turing.StepBlock.roundTM_iterate` does (the additive iteration with the cofinality bound
`t ≤ T`, H2-S finding 1), with each round replaced by the wrapped round of (ii). Finding 4 notes
that the silent iterate is not itself a theorem about the wrapper, so the fill proves the
wrapped iterate; it cites the repaired `Turing.StepBlock.roundTM_iterate` directly if H2-S
round 2 states it for a general round.
(iv) *Space.* In each round the mirrored head is at the source head's start or end cell and the
two auxiliary heads stay in `[-B, B]` with `B := 50·(|tableBitsK| + 1)`
(`Turing.StepBlock.roundTM_visited`); the leaf moves no head. So the mirrored tape visits only
cells the coded machine visits, at most `s`; the auxiliary tapes at most `2B + 1` cells each;
the startup `B_α`. The space is at most `B_α + s + 2(2B + 1) ≤ C_α · (s + 1)`. -/
theorem exists_selfUniversal (c : EffectiveMachineCode) :
    ∃ U₀ : FinTM Bool, ∀ α : List Bool, ∃ C : ℕ, 0 < C ∧
      ∀ (w output : List Bool) (t s : ℕ),
        (c.decode α).toFinTM.ComputesInTime (pairEncode α w) output t →
        (c.decode α).toFinTM.tm.spaceUsed
            ((c.decode α).toFinTM.tm.initCfg (pairEncode α w)) t ≤ s →
          ∃ t' : ℕ, U₀.ComputesInTime (pairEncode α w) output t' ∧
            U₀.tm.spaceUsed (U₀.tm.initCfg (pairEncode α w)) t' ≤ C * (s + 1) := by
  sorry

end Turing
