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
  space under any choice word is the deterministic space at that time (proved;
  the measure-transfer obligation behind `SPACE ⊆ NSPACE`).
* `Turing.NDTM.spaceUsedWith_append_of_halt` — once a branch has halted, extending
  the choice word does not change the space (proved; the invariance that makes
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

/-- Extending a choice word preserves every position visited by its prefixes,
without any halting hypothesis.

**Proof sketch.** An old prefix index is still in the larger range, and taking
that many bits of the extended word gives the same prefix. -/
private lemma visitedWith_subset_append (tm : NDTM k Symbol State) (w w' : List Bool)
    (cfg : Cfg k Symbol State input) (i : Fin k) :
    tm.visitedWith w cfg i ⊆ tm.visitedWith (w ++ w') cfg i := by
  intro p hp
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hp
  have hjle : j ≤ w.length := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  refine Finset.mem_image.mpr ⟨j, ?_, ?_⟩
  · apply Finset.mem_range.mpr
    simp only [List.length_append]
    omega
  · rw [List.take_append_of_le_length hjle]

/-- **Space stabilizes at halting**: if the branch under `w` has halted, running
under any extension `w ++ w'` visits no further cells, so the space is unchanged.
This is why `Complexity.NSPACE` may quantify over choice words of one exact
length: all-branch halting at that length freezes every branch's space.

**Proof sketch.** For `j ≤ |w|` the prefixes agree (`List.take_append_of_le_length`
-style splitting); for `j > |w|`, `(w ++ w').take j = w ++ w'.take (j - |w|)`,
`Turing.NDTM.runWith_append` factors the run through the halted configuration,
and `Turing.NDTM.runWith_of_halt` freezes it, so the head position equals the one
at prefix `w`. The two images therefore coincide (`Finset.image_congr` after
splitting `Finset.range`), tape by tape.

**Fill appendix (C1a; short-prefix argument).** The private lemma
`visitedWith_subset_append` proves the old visited set is included in the new
one without a halting hypothesis: every old index remains in the longer range,
and the corresponding prefixes agree. In particular, a shorter choice word
can be padded to any prescribed larger length without losing visited cells.
The reverse inclusion uses the halted final position for every longer prefix.
The implementation uses `Finset.Subset.antisymm` and `Finset.mem_image` for
these inclusions, since the two image domains differ. -/
theorem spaceUsedWith_append_of_halt (tm : NDTM k Symbol State) {w : List Bool}
    {cfg : Cfg k Symbol State input} (h : (tm.runWith w cfg).state = none)
    (w' : List Bool) : tm.spaceUsedWith (w ++ w') cfg = tm.spaceUsedWith w cfg := by
  unfold spaceUsedWith
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg Finset.card
  apply Finset.Subset.antisymm
  · intro p hp
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hp
    by_cases hjle : j ≤ w.length
    · refine Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (by omega), ?_⟩
      rw [List.take_append_of_le_length hjle]
    · refine Finset.mem_image.mpr ⟨w.length, Finset.mem_range.mpr (by omega), ?_⟩
      rw [List.take_length, List.take_append, List.take_of_length_le (by omega),
        runWith_append, runWith_of_halt _ h]
  · exact visitedWith_subset_append tm w w' cfg i

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
  unfold NDTM.spaceUsedWith MultiTapeTM.spaceUsed
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg Finset.card
  apply Finset.image_congr
  intro j hj
  change (tm.toNDTM.runWith (w.take j) cfg).workTapePos i =
    (tm.runFrom cfg j).workTapePos i
  rw [MultiTapeTM.toNDTM_runWith,
    List.length_take_of_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))]

end Turing
