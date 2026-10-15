# 12.2c T1 item 7 — CH7-D1 block-loop refactor

Completed Tasks 1–4 by landing the three reference files verbatim. All required checks pass. **new copies: none**.

## Provenance and scope

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`; source branch: `complexity/arora-barak-ch3-4`.
- Base: `199644473a34b6da24862d94ae1eece7f8138005`. `git merge-base --is-ancestor 1a0013d9750a6d760b6fd46b3c267fe18f08f4fa HEAD` passed before branching.
- Delivery branch: `refactor/12.2c-t1-blockloop`; commit: `6008127069b310c104c3f27c1b21137683d8bf7c`. No rebase, push or PR.
- The owned sources were unchanged since `5ad155ee` (empty `unchanged-since-issue.diff`). Only `TCSlib/Complexity/ClassNP/PolyTimeBlock{Loop,Tests,Majority}.lean` changed in the commit. Imports are byte-identical.
- Read the entire binding brief and policy, plan §4d item 7 and §4e, backlog CH7-D1, the ledger row, R2-2, and all three reference sources. No implementation deviates from the probe; no proof was shortened.
- Escalations: **none**. Item 6, `Build/EmitIter*`, `PClosure`, and all other source files remain outside this change.

## Tasks and size changes

1. Added the shared countdown layer in `Complexity.BlockLoop` in Loop: 17 publics and two private guards, directly after the emit-iteration combinator.
2. Added the three-public OR-flag engine in Tests. XOR-then-OR supplies only its test, mask and remainder operations. The plain OR test composes the XOR test with an all-false mask; its old loop and wrappers are deleted.
3. Majority uses the shared countdown step, emission and output contracts, retaining the vote-specific computation. The two private definitions are definitionally equal to their old bodies.
4. The XOR transducer uses `polyTimeComputable_of_loop` and the common orbit-length bound. Its private iterate-length lemma is deleted, and its step-computability proof has the reference two-`have` form.

| File | Lines before → after (delta) | Public before → after | Private before → after |
|---|---:|---:|---:|
| `PolyTimeBlockLoop.lean` | 500 → 789 (+289) | 22 → 39 | 10 → 11 |
| `PolyTimeBlockTests.lean` | 653 → 228 (-425) | 3 → 6 | 22 → 2 |
| `PolyTimeBlockMajority.lean` | 469 → 243 (-226) | 1 → 1 | 13 → 5 |
| Total | 1,622 → 1,260 (−362) | 26 → 46 (+20) | 45 → 18 (−27) |

## Statement freeze and declaration inventory

All 26 base public statement substrings (including whitespace and binder order) are byte-identical. Of these, 22 full declaration bodies and their docstrings are byte-identical, including all six base definitions and `blockAt`. The other four retain the same prose before the **Proof sketch** paragraph. Full final-file SHA-256 hashes match the supplied reference files.

The four changed public proofs are `polyTimeComputable_xorD`, `polyTimeComputable_blockAnyTest`, `polyTimeComputable_blockXorAnyTest`, and `polyTimeComputable_blockMajorityTest`. The OR theorem moves after the XOR theorem as sanctioned.

### Added declarations (24: 20 public, 4 private)

**PolyTimeBlockLoop.lean**

- `Complexity.BlockLoop.emit` (public).
- `Complexity.BlockLoop.flatMap_emit_orbit` (public).
- `Complexity.BlockLoop.iterate_done` (public).
- `Complexity.BlockLoop.length_iterate_le_of_slack` (public).
- `Complexity.BlockLoop.length_step_le` (public).
- `Complexity.BlockLoop.loop_output` (public).
- `Complexity.BlockLoop.lt_polyBudget_of_le` (public).
- `Complexity.BlockLoop.orbit` (public).
- `Complexity.BlockLoop.polyTimeComputable_countdown` (public).
- `Complexity.BlockLoop.polyTimeComputable_countdownInit` (public).
- `Complexity.BlockLoop.polyTimeComputable_countdownNil` (private).
- `Complexity.BlockLoop.polyTimeComputable_emit` (public).
- `Complexity.BlockLoop.polyTimeComputable_headNil` (private).
- `Complexity.BlockLoop.polyTimeComputable_of_loop` (public).
- `Complexity.BlockLoop.polyTimeComputable_step` (public).
- `Complexity.BlockLoop.sliceDropAt_pairEncode_drop` (public).
- `Complexity.BlockLoop.sliceTakeAt_pairEncode_drop` (public).
- `Complexity.BlockLoop.step` (public).
- `Complexity.BlockLoop.step_done` (public).

**PolyTimeBlockTests.lean**

- `Complexity.BlockLoop.any_range_succ_flag` (public).
- `Complexity.BlockLoop.length_flag_le` (public).
- `Complexity.BlockLoop.polyTimeComputable_orLoop` (public).
- `Complexity.zipWith_xor_blockAt` (private).
- `Complexity.zipWith_xor_self` (private).

### Deleted declarations (31, all private)

**PolyTimeBlockLoop.lean**

- `Complexity.length_xorPairStep_iterate` (private).

**PolyTimeBlockTests.lean**

- `Complexity.anyEmit` (private).
- `Complexity.anyInit` (private).
- `Complexity.anyLoop_output` (private).
- `Complexity.anyStep` (private).
- `Complexity.anyStep_done` (private).
- `Complexity.anyStep_orbit` (private).
- `Complexity.anyStep_orbit_done` (private).
- `Complexity.length_anyStep_iterate` (private).
- `Complexity.length_anyStep_le` (private).
- `Complexity.length_xorStep_iterate` (private).
- `Complexity.length_xorStep_le` (private).
- `Complexity.polyTimeComputable_anyEmit` (private).
- `Complexity.polyTimeComputable_anyInit` (private).
- `Complexity.polyTimeComputable_anyStep` (private).
- `Complexity.polyTimeComputable_xorInit` (private).
- `Complexity.polyTimeComputable_xorStep` (private).
- `Complexity.xorInit` (private).
- `Complexity.xorLoop_output` (private).
- `Complexity.xorStep` (private).
- `Complexity.xorStep_done` (private).
- `Complexity.xorStep_orbit` (private).
- `Complexity.xorStep_orbit_done` (private).

**PolyTimeBlockMajority.lean**

- `Complexity.length_majStep_iterate` (private).
- `Complexity.length_majStep_le` (private).
- `Complexity.majStep_done` (private).
- `Complexity.majStep_orbit` (private).
- `Complexity.majStep_orbit_done` (private).
- `Complexity.polyTimeComputable_majEmit` (private).
- `Complexity.polyTimeComputable_majInit` (private).
- `Complexity.polyTimeComputable_majStep` (private).

### Changed existing private declarations

`polyTimeComputable_xorPairStep` and `majLoop_output` retain byte-identical statements and receive exactly the reference proofs. All other surviving private declarations are unchanged except the following sanctioned redefinitions.

**Complexity.majEmit**

Before:
```lean
private def majEmit (s : List Bool) : List Bool
```
After:
```lean
private def majEmit : List Bool → List Bool
```

**Complexity.majStep**

Before:
```lean
private noncomputable def majStep (V : Language Bool) (a k : ℕ) (s : List Bool) : List Bool
```
After:
```lean
private noncomputable def majStep (V : Language Bool) (a k : ℕ) : List Bool → List Bool
```

`majStep` is now `BlockLoop.step (fun _ _ => [true])` with the vote-push remainder update. `majEmit` is `BlockLoop.emit` with the vote comparison. Both have the same elaborated type and value as before; the supplied two `rfl` checks were replayed successfully.

## Duplication governance

Unmodified `audits/evidence/retrofit/copy-text-screen.py` was run on the baseline and final source trees. Its four required raw outputs are included. Counts concern declarations whose extracted bodies meet the screen’s length cutoff, not all declarations.

| Screen | Declarations before → after | Pairs before → after | Reproduced characters before → after |
|---|---:|---:|---:|
| Six files | 104 → 94 | 125 → 41 | 47,734 → 10,045 |
| Owned three | 60 → 50 | 102 → 18 | 41,608 → 3,919 |

The six-file cross-file pair count falls from 65 to 2. Both remaining pairs pre-existed and are outside CH7-D1: `PClosure::union_mem_P ← PolyTimeBlockLoop::polyTimeComputable_or` (68%) and `← polyTimeComputable_not` (52%). Tests and Majority occur in no final pair.

The three-file result consists of Loop’s 17 old in-file pairs and the sole new reported in-file near-duplicate: `BlockLoop.polyTimeComputable_step ← polyTimeComputable_xorPairStep`, 87/148 characters (59%), arising from the shared `drop 1` vocabulary. This is the exact disclosed reference pair. No new cross-file pair exists; no new in-file pair reaches 90%. Loop’s pre-existing in-file pairs, including `length_xorPairStep_le` / `length_sliceDropAt_le`, are recorded out of scope.

| File | R2-2 confirmed family before → after | Owned-three screen cross-file source/target union before → after |
|---|---:|---:|
| Tests | ≥12/25 → 0/8 | 22/25 → 0/8 |
| Majority | ≥8/14 → 0/6 | 12/14 → 0/6 |
| Loop | ≥1/32 → 0/50 | 6/32 → 0/50 |

The census table uses the owned-three screen, as in the brief’s 6/32 → 0/50 Loop row. Across all six files the Loop union is instead 8/32 → 2/50, because its two Boolean helpers participate in the explicitly excluded, pre-existing PClosure pairs. The R2-2 source-inclusive family vanishes because the duplicated guards, countdown, length, orbit, initializer and single-emission proofs are replaced by shared citations, and the obsolete OR/XOR/majority wrappers are deleted. The shared generic layer is counted once; Loop’s disclosed in-file convention does not add family members.

For the rename rerun, the three files were copied into temporary trees, and the Majority copy was processed with `sed -e 's/maj/any/g' -e 's/blockMajorityTest/blockAnyTest/g'` before the same three-file screen. Raw before and after outputs are included:

```text
declarations screened: 60; copy pairs (target reproduces >= half of source): 103; reproduced text: 42,567 chars
declarations screened: 50; copy pairs (target reproduces >= half of source): 18; reproduced text: 3,919 chars
```

**new copies: none**. The screen is a textual heuristic; the explicit declaration inventory and reference-conformity checks also establish the requested family collapse.

## Verification

- Lean 4.25.0; mathlib `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`; dependency pins verified.
- Ran `lake exe cache get` on the 72 direct Mathlib imports in the supplied closure; successful retry unpacked 2,783 cache files. No `lake build` was run.
- All Lean proof checks used the unmodified `scripts/lean_check_tree.sh`, which removes the previous output and requires a fresh `.olean` and no errors.
- Baseline bootstrap: **218/218 modules**, 0 errors, 1 existing sorry warning, from `briefs/orders/ch34-t1-blockloop.txt`.
- Final replay: **24/24 modules**, 0 errors, 0 sorry warnings. Owned files: **0 errors, 0 warnings, 0 sorries**. Every downstream sorry-warning line is byte-identical to the corresponding baseline line.
- Replayed the supplied pre-ship probe against the baseline: **26 public `rfl` checks + 2 private-body `rfl` checks**, 72 axiom prints, 0 errors, 0 warnings, 0 sorries.
- Printed axioms independently for the 26 baseline publics and all 46 final publics. The first 26 final print entries are byte-identical to the complete baseline output. All 46 use only `propext`, `Classical.choice`, `Quot.sound`, with no `sorryAx`.
- `git diff --check` passed; only the three owned tracked files changed.

Lint result:
```text
style_lint: 0 FAIL, 5 WARN over 19 files
```

The five lint warnings are size warnings in untouched `EXP`, `Nondeterminism`, `SAT`, `TMSAT`, and `Tautology`. The three owned files have no lint warnings; Loop’s 789-line size is the sanctioned reference size and is reported at INFO.

The 24-module replay order is included as `replay-order.txt`. It is exactly the reverse import closure of the three owned files within the supplied 218-module order, including all specified facades and 11 Karp–Lipton/Meyer modules.

Final sweep tail:
```text
END 20/24 exit=0 seconds=2.0 warnings=0
BEGIN 21/24 TCSlib/Complexity/ClassNP
END 21/24 exit=0 seconds=1.17 warnings=0
BEGIN 22/24 TCSlib/Complexity/PolyHierarchy
END 22/24 exit=0 seconds=1.12 warnings=0
BEGIN 23/24 TCSlib/Complexity/Randomized/PolyTimeModel
END 23/24 exit=0 seconds=2.04 warnings=0
BEGIN 24/24 TCSlib/Complexity/Randomized
END 24/24 exit=0 seconds=2.27 warnings=0
SUMMARY final: 24/24 modules passed; errors=0; sorry_warnings=0
```

Environment repairs were limited to local verification infrastructure. The sandbox PID namespace initially prevented Lean from locating its executable; the included `proc_self_compat.c` maps only the current process’s `/proc/<pid>/exe` query to `/proc/self/exe`. No Lean binary or kernel was modified. The first cache attempts failed from that path issue and disk pressure; the successful retry is logged. The working repository and fresh `.olean` tree used the available memory-backed filesystem. No verification gap remains.

## Quoted docstring edits

The following exact diffs quote every changed existing module or declaration docstring. New declarations’ complete docstrings are in the three full source files; deleted declarations’ docstrings disappear with those declarations.

```diff
--- PolyTimeBlockLoop module before
+++ PolyTimeBlockLoop module after
@@ -16,6 +16,8 @@
 * `Complexity.sliceTakeAt` / `Complexity.sliceDropAt` — keep the first
   component and take/drop a polynomial-length prefix of the second.
 * `Complexity.xorD` — truncating bitwise XOR of the two components of a pair.
+* `Complexity.BlockLoop.step` / `Complexity.BlockLoop.emit` — one round and the chunk
+  function of a countdown block loop.
 
 ## Main results
 
@@ -28,6 +30,10 @@
   `exists_emitCallTM`) as the per-round body.
 * `Complexity.polyTimeComputable_xorD` — truncating bitwise XOR is
   polynomial-time, via the emit-iteration loop.
+* `Complexity.BlockLoop` — the countdown block loop shared by the aggregated block
+  tests: the round `BlockLoop.step` and chunk `BlockLoop.emit`, their polynomial-time,
+  length and orbit facts, and the assembled engines
+  `BlockLoop.polyTimeComputable_countdown` and `BlockLoop.polyTimeComputable_of_loop`.
 * The aggregated one-bit block tests live in
   `TCSlib.Complexity.ClassNP.PolyTimeBlockTests`.
 
--- Complexity.polyTimeComputable_xorD docstring before
+++ Complexity.polyTimeComputable_xorD docstring after
@@ -1,6 +1,8 @@
 /-- `xorD` is polynomial-time computable.
-**Proof sketch.** An instance of `Complexity.polyTimeComputable_emitIter`:
-the loop state is the pair of not-yet-consumed components; each round emits
+**Proof sketch.** An instance of `Complexity.polyTimeComputable_emitIter`, assembled
+by `Complexity.BlockLoop.polyTimeComputable_of_loop`, with the orbit envelope from
+`Complexity.BlockLoop.length_iterate_le_of_slack`: the loop state is the pair of
+not-yet-consumed components; each round emits
 the XOR of the two head bits (nothing once either component is exhausted) and
 drops both heads, so the concatenated output is exactly the truncating
 `List.zipWith xor`.  The round budget `|z|+1` dominates the shorter
```

```diff
--- PolyTimeBlockTests module before
+++ PolyTimeBlockTests module after
@@ -5,10 +5,12 @@
 (`TCSlib.Complexity.ClassNP.PolyTimeBlockLoop`): the one-bit OR,
 strict-majority, and XOR-then-OR aggregations of a polynomial-time one-bit
 indicator over polynomially many polynomial-length blocks are polynomial-time.
-Each is an instance of `Complexity.polyTimeComputable_emitIter` with the
-aggregation state (flag, vote counters, XOR mask) carried inside the loop's
-tape-resident state word; the per-round work is assembled from the existing
-`FP` combinators, and the orbit is computed in closed form by induction.
+Each is an instance of the countdown block loop `Complexity.BlockLoop`
+(`PolyTimeBlockLoop`), with the aggregation state (flag, vote counters, XOR mask)
+carried inside the loop's state word.  The XOR-then-OR test is an instance of the
+OR-flag engine `Complexity.BlockLoop.polyTimeComputable_orLoop`, supplying its per-round
+test, its remainder update and the closed form of its remainders; the plain OR test is
+the XOR-then-OR test with an all-`false` mask.
 
 These are the `PolyTimeComputable` engines of the `P`-closure lemmas
 `Complexity.mem_P_of_blockAny` / `_blockMajority` / `_blockXorAny` in
@@ -21,6 +23,8 @@
 
 ## Main results
 
+* `Complexity.BlockLoop.polyTimeComputable_orLoop` — the OR-flag block loop is
+  polynomial-time, and its output is the OR of the per-round tests.
 * `Complexity.polyTimeComputable_blockAnyTest` / `_blockXorAnyTest` — the
   aggregated one-bit OR and XOR-then-OR block tests of a polynomial-time
   one-bit indicator are polynomial-time.  The strict-majority test lives in
--- Complexity.polyTimeComputable_blockAnyTest docstring before
+++ Complexity.polyTimeComputable_blockAnyTest docstring after
@@ -3,12 +3,9 @@
 length `a·(n+1)^k` passes the test on `Turing.pairEncode`d (first component,
 block).
 
-**Proof sketch.** An instance of `Complexity.polyTimeComputable_emitIter`.
-The loop state is `pairEncode [flag] (pairEncode countdown (pairEncode x rem))`
-with a unary countdown initialized at `a'·(|x|+1)^k'`
-(`Complexity.polyTimeComputable_polyUnary`); each round ORs the indicator of
-`sliceTakeAt a k` into the flag, drops the block (`sliceDropAt a k`), and
-decrements; the chunk function emits `[flag]` exactly at countdown exhaustion
-(the step then moves to an absorbing done state), so the concatenated output
-is the single aggregated bit.  The orbit is computed in closed form by
-induction on the round index. -/
+**Proof sketch.** The XOR-then-OR test with an all-`false` mask of the block length:
+on `⟨z, 0^B⟩`, where `B = a·(|x|+1)^k`, the XOR-shifted blocks are the blocks of `z`
+themselves (each has length at most `B`), so this test is
+`Complexity.polyTimeComputable_blockXorAnyTest` composed with `z ↦ ⟨z, 0^B⟩`.  The mask
+`0^B` is computed as `xorD ⟨1^B, 1^B⟩` (`Complexity.polyTimeComputable_polyUnary`,
+`Complexity.polyTimeComputable_xorD`). -/
--- Complexity.polyTimeComputable_blockXorAnyTest docstring before
+++ Complexity.polyTimeComputable_blockXorAnyTest docstring after
@@ -3,8 +3,8 @@
 `⟨⟨x, u⟩, v⟩`; block `i` is drawn from `u`, XORed bitwise with `v`
 (truncating, `Complexity.xorD`), and tested paired with `x`.
 
-**Proof sketch.** As `Complexity.polyTimeComputable_blockAnyTest`, with the
-per-round test precomposed with the XOR mask: the loop state additionally
-carries `v`, and the round's test input is
-`pairEncode x (xorD (pairEncode v block))`
-(`Complexity.polyTimeComputable_xorD`). -/
+**Proof sketch.** An instance of `Complexity.BlockLoop.polyTimeComputable_orLoop` on
+the remainder `⟨v, ⟨x, u⟩⟩`: the round's test input is
+`pairEncode x (xorD (pairEncode v block))` (`Complexity.polyTimeComputable_xorD`,
+`Complexity.xorD_pairEncode`), the mask `v` is carried unchanged, and the block is
+dropped from `u`. -/
```

```diff
--- PolyTimeBlockMajority module before
+++ PolyTimeBlockMajority module after
@@ -3,13 +3,13 @@
 
 The strict-majority customer of the bounded block-query loop
 (`TCSlib.Complexity.ClassNP.PolyTimeBlockLoop`), split from
-`TCSlib.Complexity.ClassNP.PolyTimeBlockTests` for size: the loop state
-carries two unary vote counters, and at countdown exhaustion the emitted bit
-is their strict comparison.
+`TCSlib.Complexity.ClassNP.PolyTimeBlockTests` for size: an instance of the countdown
+block loop `Complexity.BlockLoop` whose remainder carries two unary vote counters, and
+whose chunk at countdown exhaustion is their strict comparison.
 
 ## Main definitions
 
-None — the loop state, step, and chunk functions are private to this file.
+None — the loop's round, chunk and initial state are private to this file.
 
 ## Main results
 
--- Complexity.majLoop_output docstring before
+++ Complexity.majLoop_output docstring after
@@ -1,4 +1,7 @@
 /-- The majority loop's machine-level output is the single aggregated bit.
-**Proof sketch.** As the OR output lemma; at exhaustion the emitted
-comparison of the unary counters `¬(cT ≤ K - cT)` is the strict majority
-`K < 2·cT`, by `decide_not` and arithmetic. -/
+**Proof sketch.** `Complexity.BlockLoop.loop_output` with the live marker as every head
+and remainders `⟨⟨1^cT i, 1^(i - cT i)⟩, ⟨x, rem.drop (i·B)⟩⟩`, where `cT i` counts the
+passing blocks among the first `i` (`List.countP_append` at `List.range_succ`): the vote
+push adds the `i`-th block's vote and the block is dropped.  At exhaustion the emitted
+comparison of the unary counters `¬(cT ≤ K - cT)` is the strict majority `K < 2·cT`, by
+`decide_not` and arithmetic. -/
--- Complexity.majStep docstring before
+++ Complexity.majStep docstring after
@@ -2,4 +2,5 @@
 `pairEncode [true] (pairEncode countdown (pairEncode (pairEncode uT uF)
 (pairEncode x rem)))`: push one vote onto the passed (`uT`) or failed (`uF`)
 unary counter according to the indicator of the current block, drop the
-block, decrement the countdown. -/
+block, decrement the countdown.  An instance of `Complexity.BlockLoop.step` with the
+live marker `[true]` as head. -/
--- Complexity.polyTimeComputable_blockMajorityTest docstring before
+++ Complexity.polyTimeComputable_blockMajorityTest docstring after
@@ -1,9 +1,11 @@
 /-- The strict-majority-aggregated block test of a polynomial-time one-bit
 indicator is polynomial-time.
 
-**Proof sketch.** As `Complexity.polyTimeComputable_blockAnyTest`, with the
-flag replaced by two unary vote counters (passed and failed blocks); at
-countdown exhaustion the emitted bit is the strict comparison of their
-lengths (`Complexity.polyTimeComputable_lenLe` after a `pairSwap`), which
-equals `a'·(n+1)^k' < 2·(passed votes)` since the counts sum to the round
-total. -/
+**Proof sketch.** `Complexity.BlockLoop.polyTimeComputable_countdown` for the countdown
+block loop whose head is the live marker and whose remainder carries two unary vote
+counters (passed and failed blocks); the vote push is an `ite` on the block's indicator;
+at countdown exhaustion the emitted bit is the strict comparison of their lengths
+(`Complexity.polyTimeComputable_lenLe` after a `pairSwap`), which equals
+`a'·(n+1)^k' < 2·(passed votes)` since the counts sum to the round total.  The vote push
+grows the counters by at most four symbols (`length_majVote_le`), well within the
+slack `16`. -/
```

## Final 46 axiom prints

```text
'Complexity.sliceTakeAt' depends on axioms: [propext]
'Complexity.sliceDropAt' depends on axioms: [propext]
'Complexity.polyTimeComputable_sliceTakeAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.polyTimeComputable_sliceDropAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.polyTimeComputable_tail' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.polyTimeComputable_isNil' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.polyTimeComputable_or' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.polyTimeComputable_not' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.pairFstD_nil' does not depend on any axioms
'Complexity.length_pairSndD_le' depends on axioms: [propext, Quot.sound]
'Complexity.eq_pairEncode_of_pairFstD_ne' depends on axioms: [propext, Quot.sound]
'Complexity.length_pair_components_le' depends on axioms: [propext, Quot.sound]
'Complexity.length_sliceDropAt_le' depends on axioms: [propext, Quot.sound]
'Complexity.flatMap_range_eq_single' depends on axioms: [propext, Quot.sound]
'Complexity.blockDone' does not depend on any axioms
'Complexity.isNilB' does not depend on any axioms
'Complexity.polyTimeComputable_take1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.polyTimeComputable_headD' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.polyTimeComputable_emitIter' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.xorD' does not depend on any axioms
'Complexity.polyTimeComputable_xorD' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.xorD_pairEncode' depends on axioms: [propext, Quot.sound]
'Complexity.blockAt' depends on axioms: [propext]
'Complexity.polyTimeComputable_blockAnyTest' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.polyTimeComputable_blockXorAnyTest' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.polyTimeComputable_blockMajorityTest' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.BlockLoop.step' does not depend on any axioms
'Complexity.BlockLoop.emit' does not depend on any axioms
'Complexity.BlockLoop.polyTimeComputable_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.BlockLoop.polyTimeComputable_emit' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.BlockLoop.polyTimeComputable_countdownInit' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.BlockLoop.step_done' depends on axioms: [propext, Quot.sound]
'Complexity.BlockLoop.length_step_le' depends on axioms: [propext, Quot.sound]
'Complexity.BlockLoop.length_iterate_le_of_slack' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.BlockLoop.sliceTakeAt_pairEncode_drop' depends on axioms: [propext, Quot.sound]
'Complexity.BlockLoop.sliceDropAt_pairEncode_drop' depends on axioms: [propext, Quot.sound]
'Complexity.BlockLoop.orbit' depends on axioms: [propext, Quot.sound]
'Complexity.BlockLoop.iterate_done' depends on axioms: [propext, Quot.sound]
'Complexity.BlockLoop.lt_polyBudget_of_le' depends on axioms: [propext, Quot.sound]
'Complexity.BlockLoop.flatMap_emit_orbit' depends on axioms: [propext, Quot.sound]
'Complexity.BlockLoop.loop_output' depends on axioms: [propext, Quot.sound]
'Complexity.BlockLoop.polyTimeComputable_of_loop' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.BlockLoop.polyTimeComputable_countdown' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.BlockLoop.length_flag_le' depends on axioms: [propext]
'Complexity.BlockLoop.any_range_succ_flag' depends on axioms: [propext]
'Complexity.BlockLoop.polyTimeComputable_orLoop' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Package

The ZIP contains this report; three full final sources; a one-commit `git format-patch` series; an incremental Git bundle requiring the recorded base; baseline/final sweep and axiom logs; the four required screen outputs and two rename outputs; lint, freeze and scope evidence; reproduction scripts; and `SHA256SUMS`. The bundle and patch have the same commit and touch only the three owned files.

Apply the patch on the recorded base, or fetch `refactor/12.2c-t1-blockloop` from the bundle in a repository containing that base. Integration and the separate audit gate remain the maintainer’s workflow.
