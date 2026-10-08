/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Nondeterministic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Space usage of nondeterministic machines

The space measure for binary-choice NDTMs, mirroring the deterministic
`Turing.MultiTapeTM.visitedByTapeHead`/`spaceUsedByTape`/`spaceUsed` along
choice-word runs: the cells a work-tape head visits during the run under a given
choice word, summed over the work tapes. This is the campaign convention for
[AB09, Definition 4.1]'s nondeterministic clause — **visited** cells, the same
measure as the deterministic `SPACE` ([AB09]'s own wording switches to "nonblank"
locations for `NSPACE`; the split and the convention are recorded in
`TCSlib.Complexity.SpaceComplexity.Basic`). The class `Complexity.NSPACE` built on
this measure lives in `TCSlib.Complexity.SpaceComplexity.NSPACE`.

## Main definitions

* `Turing.NDTM.visitedWith` — the set of cells visited by one work-tape head
  along the run under a choice word (prefixes included).
* `Turing.NDTM.spaceUsedWith` — total visited cells, summed over work tapes.
  [AB09, Definition 4.1, nondeterministic clause, visited-cells convention]

## Main results

* `Turing.NDTM.visitedWith_nil` — the empty run visits the starting positions.
* `Turing.MultiTapeTM.toNDTM_spaceUsedWith` — the embedded deterministic machine's
  space under any choice word is the deterministic space at that time (sorried;
  the measure-transfer obligation behind `SPACE ⊆ NSPACE`).
* `Turing.NDTM.spaceUsedWith_append_of_halt` — once a branch has halted, extending
  the choice word does not change the space (sorried; the invariance that makes
  the exact-length quantifier in `Complexity.NSPACE` sufficient).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1, Definition 4.1.)
-/

namespace Turing

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

namespace NDTM

/-- The cells visited by the head of work tape `i` along the run of `tm` under the
choice word `w` from `cfg`: the head positions after every prefix of `w` (the empty
prefix included, so the starting position always counts) — the nondeterministic
counterpart of `Turing.MultiTapeTM.visitedByTapeHead`. -/
def visitedWith (tm : NDTM k Symbol State) (w : List Bool)
    (cfg : Cfg k Symbol State input) (i : Fin k) : Finset ℤ :=
  (Finset.range (w.length + 1)).image fun j => (tm.runWith (w.take j) cfg).workTapePos i

/-- The space used by `tm` along the run under the choice word `w` from `cfg`: the
number of visited cells, summed over the work tapes — the nondeterministic
counterpart of `Turing.MultiTapeTM.spaceUsed`, for one branch. The input tape
(read-only) and the output tape (append-only) do not count.
[AB09, Definition 4.1, nondeterministic clause, visited-cells convention] -/
def spaceUsedWith (tm : NDTM k Symbol State) (w : List Bool)
    (cfg : Cfg k Symbol State input) : ℕ :=
  ∑ i, (tm.visitedWith w cfg i).card

/-- The empty choice word visits exactly the starting position of each head. -/
@[simp]
lemma visitedWith_nil (tm : NDTM k Symbol State) (cfg : Cfg k Symbol State input)
    (i : Fin k) : tm.visitedWith [] cfg i = {cfg.workTapePos i} := by
  simp [visitedWith]

/-- **Space stabilizes at halting**: if the branch under `w` has halted, running
under any extension `w ++ w'` visits no further cells, so the space is unchanged.
This is why `Complexity.NSPACE` may quantify over choice words of one exact
length: all-branch halting at that length freezes every branch's space.

**Proof sketch.** For `j ≤ |w|` the prefixes agree (`List.take_append_of_le_length`
-style splitting); for `j > |w|`, `(w ++ w').take j = w ++ w'.take (j - |w|)`,
`Turing.NDTM.runWith_append` factors the run through the halted configuration,
and `Turing.NDTM.runWith_of_halt` freezes it, so the head position equals the one
at prefix `w`. The two images therefore coincide (`Finset.image_congr` after
splitting `Finset.range`), tape by tape. -/
theorem spaceUsedWith_append_of_halt (tm : NDTM k Symbol State) {w : List Bool}
    {cfg : Cfg k Symbol State input} (h : (tm.runWith w cfg).state = none)
    (w' : List Bool) : tm.spaceUsedWith (w ++ w') cfg = tm.spaceUsedWith w cfg := by
  sorry

end NDTM

/-- The embedded deterministic machine's space along any choice word is its
deterministic space at the corresponding time: `toNDTM` ignores its choices
(`Turing.MultiTapeTM.toNDTM_runWith`), so the visited sets coincide prefix by
prefix. The measure-transfer obligation behind `Complexity.SPACE_subset_NSPACE`.

**Proof sketch.** Fix a tape `i`. For every `j ≤ |w|`,
`tm.toNDTM.runWith (w.take j) cfg = tm.runFrom cfg j` by
`Turing.MultiTapeTM.toNDTM_runWith` and `List.length_take_of_le`, so the images
defining `Turing.NDTM.visitedWith` and `Turing.MultiTapeTM.visitedByTapeHead`
agree pointwise on `Finset.range (|w| + 1)` (`Finset.image_congr`), and the card
sums agree. -/
theorem MultiTapeTM.toNDTM_spaceUsedWith (tm : MultiTapeTM k Symbol State)
    (w : List Bool) (cfg : Cfg k Symbol State input) :
    tm.toNDTM.spaceUsedWith w cfg = tm.spaceUsed cfg w.length := by
  sorry

end Turing
