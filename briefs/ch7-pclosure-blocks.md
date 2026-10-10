# Brief: block-query closure of `P` (shared composition primitive)

**Status:** coordination proposal (not yet scheduled fill). Rides the ch7 → ch3-4
coordination PR. Target branch for the eventual fill: the shared `complexity/arora-barak-ch3-4`.

## Why this exists

`Randomized/PolyTimeModel.lean`'s three open closures — `polyTimeModel_closedUnderMajority`,
`_closedUnderAny`, `_closedUnderShiftOr` — all reduce to one missing, **chapter-neutral**
fact: *`P` is closed under running a `P`-decider on a polynomial number of fixed-size
blocks of the input and aggregating the answers* (OR / strict-majority / XOR-then-OR).
The library has pointwise `P`-closure (`PClosure.lean`: preimage, ∩, ∪, complement,
finite `mem_P_of_atoms`) but **no** "polynomially-many `P`-queries with aggregation"
closure (the earlier infra survey confirmed: an `OracleTM` type exists, but no `P^P = P`
style lemma anywhere). ch3-4's closure/composition work needs the same primitive, so it
is built **once** here and consumed by both.

## Placement (per policy §1)

* **Headline closure lemmas → extend `TCSlib/Complexity/ClassNP/PClosure.lean`** (the
  `P`-closure home; 183 lines now, room to grow; `mem_P_of_*` naming). *This modifies a
  frozen, audited Chapter-1/2 file — flag it for audit per standing practice.*
* **Heavy machinery → a new general helper `TCSlib/Complexity/ClassNP/PolyTimeBlockLoop.lean`**
  (namespace `Complexity`), imported by `PClosure.lean`, so the closure file stays a
  statements layer and the loop/aggregator proofs don't blow its size budget. Reuses the
  existing general pieces: `PolyTimePrefix` (take/drop at a length), `CounterProgInput`,
  `TuringMachine/Build/Loop.lean` (the bounded `emit`/`find` loop combinators),
  `test_of_mem_P`/`mem_P_of_test`.
* `Randomized/PolyTimeModel.lean` stays a **thin consumer** — the three `closedUnder*`
  discharges become a few lines each, exactly as `closedUnderRace` reduced to the slice
  primitives.

## Sub-obligations (general, reusable)

1. **Block extraction, poly-time.** `fun w i => (pairSndD w).drop (i * q |pairFstD w|) |>.take (q |pairFstD w|)` and the re-paired `pairEncode (pairFstD w) (that block)` are `PolyTimeComputable` in `w` for each loop index, with `q` a `polyLen` schedule. Generalizes `PolyTimePrefix.take/drop` from a single prefix to the `i`-th block.
2. **Bitwise XOR, poly-time.** `fun p => List.zipWith xor (pairFstD p) (pairSndD p)` is `PolyTimeComputable` (truncating on unequal lengths — see the audited ch7-phase1 finding 1). Needed only for `shiftOr`.
3. **Bounded aggregation loop.** Given `V ∈ P` (hence its indicator is `PolyTimeComputable` by `test_of_mem_P`), the counts/flags
   * `fun w => (List.range (k |pairFstD w|)).countP (fun i => blockTest V w i)` and
   * `fun w => (List.range (k |pairFstD w|)).any (fun i => blockTest V w i)`

   are `PolyTimeComputable`, via a `Build/Loop.lean` host that installs the `P`-decider as
   the per-round call (the pattern the repaired `PolyTimePrefix` counter program already
   uses). This is the one genuinely new combinator.

## Headline lemmas to add to `PClosure.lean`

Stated for an arbitrary per-block `P`-language `V` and `polyLen` schedules `q = polyLen a k`,
`K = polyLen a' k'` (sketch signatures; final forms agreed with ch3-4):

```
theorem mem_P_of_blockAny     (hV : V ∈ P) (a k a' k') :
  { w | ∃ i < K |pairFstD w|, pairEncode (pairFstD w) (block q w i) ∈ V } ∈ P
theorem mem_P_of_blockMajority (hV : V ∈ P) (a k a' k') :
  { w | K |pairFstD w| < 2 * ((List.range (K |pairFstD w|)).countP
          (fun i => decide (pairEncode (pairFstD w) (block q w i) ∈ V))) } ∈ P
theorem mem_P_of_blockXorAny  (hV : V ∈ P) (a k a' k') :   -- nested pair ⟨⟨x,u⟩,v⟩, for shiftOr
  { w | ∃ i < K …, pairEncode x (List.zipWith xor v (block q u i)) ∈ V } ∈ P
```

## How the three closures reduce (thin, in `PolyTimeModel.lean`)

* `closedUnderAny`: the some-true set of `anyVerifier M (polyLen a k) (polyLen a' k')` is
  exactly `mem_P_of_blockAny` instantiated at `V = M`'s some-true `P`-language; some-false
  set is its complement (`compl_mem_P`). (Same off-pair-freedom argument as
  `closedUnderRace`.)
* `closedUnderMajority`: some-true set = `mem_P_of_blockMajority`; some-false = complement.
* `closedUnderShiftOr` (two-witness): the `EffTwoWitness` set = `mem_P_of_blockXorAny` on
  the nested `pairEncode (pairEncode x u) v`.

## Verification

Per `workflow.md §6`: `scripts/lean_check_tree.sh` green on `PClosure.lean`, the new helper,
and `PolyTimeModel.lean`; `#print axioms` on the three `closedUnder*` and the downstream
`adleman_polyTime`/`sipser_gacs_polyTime` showing `[propext, Classical.choice, Quot.sound]`
once filled (no `sorryAx`). Then the only remaining ch7 admission is the intentional
Thm 7.41.

## Coordination note for ch3-4

If ch3-4 already has a block-loop / P-query-composition combinator, we adopt theirs and
delete this (or vice versa) — the goal is one shared primitive, not two. The headline
`mem_P_of_block*` names and the `PolyTimeBlockLoop` helper are proposals open to their
conventions.
