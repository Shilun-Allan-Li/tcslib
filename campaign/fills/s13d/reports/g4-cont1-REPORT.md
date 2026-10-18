# §13d G4, continuation 1 — partial fill

**Partial delivery. Both machine-row targets remain open.** Phase 0's four mandatory
re-pointings are complete. Phase 1 has the two layout bridges, offset formulas and seek
precondition proofs. Phase 2 has the total cascade's pure side-pass reordering, but no new
machine scan, column move, pass, home move or cleanup. No helper admission is added.

## Pin and input checks

Base: `94b986d4db7167ab2a8b20d38d4385f11e60be0e`. The clone first checked out
`complexity/arora-barak-ch3-4` at `c487ef9d1a353c53a9e57f560899e9e0a00720a5`.
`git merge-base --is-ancestor 94b986d4db7167ab2a8b20d38d4385f11e60be0e HEAD`
succeeded there. Branch `fill/s13d-g4-cont1` was then created at exactly the base.
No rebase, merge, cherry-pick, push or PR was performed.

| Input | Verified SHA-256 |
|---|---|
| `s13d-fill-g4-cont1.md` | `cd1809a741f893024d3e4482cd0729e8615ec9ca858edd8cd54db54291c3102d` |
| Environment addendum | `a25474c52b6b8e8bc1295fad48278b3356b8fed482d2e49c5874554f6d8d2928` |

The repository brief matches the attachment byte for byte after replacing `@ANCESTOR@`
with the base. The repository addendum matches its attachment. Only declarations available
at this base were used; no in-flight fill or later API source was consumed.

## Changed and new declarations

The four inherited changes preserve their statements:

| Helper | Replacement dependencies |
|---|---|
| `zr_read_slot` | `zoneSlotOf_inr`, `Option.map_some`; the same published left/right cell lemmas |
| `zr_capacity_pos` | `zoneCapacity_eq`, then `Nat.mul_pos` and `Nat.two_pow_pos` |
| `zr_ruler_length` | `zoneCapacity_eq` replaces unfolding `zoneCapacity` |
| `zr_mirror_tape` | `zonedTape_zero`, `zonedTape_of_pos`, `zonedTape_of_neg`, `zoneCellAt_eq`, `ZoneContents.words_true/false`, `ZoneContents.swap_home/left/right` |

No other inherited private declaration is changed or removed. Both permitted fill
appendices are updated. The public statements, target bodies, imports, module header,
data, envelopes and endpoint lemmas remain unchanged.

All new declarations are private, in the prescribed home, with the `zr_` prefix:

| Declaration | Role |
|---|---|
| `zr_fieldsTape_eq` | One shared comparison argument: agreement on every field and its right separator gives agreement below the final offset. Uses `fieldsTape_field`; it does not reconstruct the layout's implementation. |
| `zr_right_offset` | Right layout field `i+1` begins at `zoneStart i`, including the end offset. |
| `zr_zonedTape_right_fields` | The recommended right bridge, with exactly its interval and field list. |
| `zr_left_offset` | Left prefix offset plus the remaining zone extent equals the whole extent. |
| `zr_zonedTape_left_fields` | The recommended reversed left bridge, including positions `-2` and `-1` and the zero-level case. |
| `zr_zoneCells_ne_nil` | Every physical zone is a nonempty field, even if its virtual slots are empty. |
| `zr_seekEnd_pre` | Discharges the complete published seek-to-end precondition from `zoneRowPre`. |
| `zr_seekStart_pre` | Discharges the complete published seek-to-start precondition from `zoneRowPre`. |
| `zr_left_two_walks` | Exact arithmetic evidence for escalation E1 below. |
| `zr_shift_commute` | Right inward and left outward shifts commute, including all guards. |
| `zr_inPass_out` | Extends that commutation to a whole right pass and one left shift. |
| `zr_pair_pass` | One shared reordering for an arbitrary list of guarded pairs. |
| `zr_cascade_passes` | Applies the public cascade equation and the shared reordering to the descending and ascending lists, keeping the guarded home move between them. |

The reordering makes no fullness, donor, room or positive-level assumption. It therefore
applies to the total cascade, rather than only its classical-input behavior. No machine host,
transition table, extra tape, new leaf or ruler builder is introduced.

## Escalation E1 (this continuation): left extension starts one cell too far right

The continuation's phase-1 route says to run `seekStartTM` from home, then make two
adjusted leftward walks of length `2^ℓ`, and write the new zone outer half first.
The published seek endpoint and the proved left offset give the initial position
`2 - zoneStart ℓ`. The two walks reach

```text
2 - zoneStart ℓ - 2·2^ℓ
  = 2 - zoneStart ℓ - zoneCapacity ℓ
  = -(zoneStart ℓ + zoneCapacity ℓ - 1) + 1.
```

The specified outermost cell is `-(zoneStart ℓ + zoneCapacity ℓ - 1)`. Thus the prescribed
position is one cell too far right. `zr_left_two_walks` is the Lean-checked general equality.
For `ℓ = 1`, the old first cell is `-3`, the two walks reach `-7`, and the new outermost cell
is `-8`. Starting the four-cell write at `-7` would also overwrite separator `-4` and omit `-8`.

**Ground rule 4 disposition:** stop on this left-pass composition and record the obstruction.
Neither frozen target is changed. No claim is made that either target is false.
A possible route amendment is one additional leftward one-cell move, with its control cost,
envelope and eventual restoration accounted for. That amendment is proposed here, not
implemented. No missing external equation was encountered in the proved components.

## Open declarations and continuation work

### `Turing.exists_zoneExtendTM`

**Proof sketch.** Use the checked right bridge and seek precondition; handle level zero
with the inherited one-cell leaf; for positive levels copy the preceding zone to a scratch
ruler, compose the two mapped half-writes, and return home using the public round and
composition hosts. Resolve E1 before the left-side write; clear the ruler, restore both
heads, and assemble the prescribed envelope via `Contract.ofSegment`. The ruler builder,
composed right pass, return-home rounds, left pass and cleanup have not been constructed.

### `Turing.exists_zoneRebalanceTM`

**Proof sketch.** Build the two-exit feeding-side scan with `round_iff` and `Round.iterate`,
using the inherited slot tests and scan-index facts. Construct the guarded column operation
at one level through mapped copy, scan and writeback contracts. Use `zr_cascade_passes` to
organize the descending and ascending operations into separate side passes around the
guarded home move. Clear scratch, restore heads and use the geometric cost and frame
lemmas to construct the specified contract. The machine scan with `short`, pair step,
machine passes, home move and cleanup are all still open.

Both rows retain their original literal `sorry` bodies. Their admission walks must and do
reach `sorryAx` only through their own bodies; no new helper carries an admission.

## Scratch layout and walk convention

This continuation constructs no machine scratch layout. The new seek-precondition proofs
apply to tape 0; no ruler, column buffer or unary count is allocated. The inherited
`zr_ruler_tail` remains unchanged: for a ruler of positive length `m`, advance the ruler
head once alone, then walk its tail of length `m-1`. The moved heads travel exactly `m`,
while the ruler head has advanced `m+1` from its initial position. Displacement zero still
requires a stationary branch, and ruler restoration and dispatch costs remain outstanding.
E1 uses this exact displacement convention, not an alternative walk interpretation.

## Promotion candidates

| Candidate | Contract or mathematical interface |
|---|---|
| Inherited `zr_cellTM` / `zr_cellContract` | Exact time one; optional write and one head move; two live slot-dependent verdicts; endpoint-hull envelope. |
| Inherited `zr_ruler_tail` | Directed word premise after the one-cell ruler-head adjustment. |
| Inherited `zr_mirror_tape` | Swapping all track sides equals reflecting physical coordinates about home. |
| `zr_fieldsTape_eq` | A common field-layout comparison lemma over a tape and a field list. |
| Both `zr_zonedTape_*_fields` bridges and offset formulas | The specified bounded field-layout equalities; `zr_seekEnd_pre` and `zr_seekStart_pre` prove their fit to the public row contracts. |
| `zr_pair_pass` / `zr_cascade_passes` | Total guarded pair-pass reordering, with the home move left in place. |

No new named machine or ruler-builder candidate exists. No contiguous layout-copy helper
overlaps the in-flight F3 clock writer. No private host or private Catalog declaration is cited.

## Runtime

The unmodified pinned Lean executable failed with `error: failed to locate application`.
The attached addendum's exact C source was then compiled and preloaded only for Lean/Lake
checks. Its SHA-256 is
`985924ad83d39e108c0a2107bab07e65cdeb88641453508ab5acda115534fba7`.
The source is included under `evidence/runtime/`; the compiled `.so` is excluded.

The per-process environment was:

```sh
PATH=/workspace/scratch/edcf4c9982ed/runtime/lean-4.25.0-linux/bin:$PATH
LEAN_SYSROOT=/workspace/scratch/edcf4c9982ed/runtime/lean-4.25.0-linux
LAKE_HOME=/workspace/scratch/edcf4c9982ed/runtime/lean-4.25.0-linux
LD_PRELOAD=/workspace/scratch/9287e0d90bc1/evidence/runtime/executable-path.so
```

This starts Lean 4.25.0, commit `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`.
Mathlib is exactly `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`; all 11 materialized
dependency repositories match their manifest pins. No Lean binary, kernel, source or
filesystem permission was modified for startup.

The authorized `lake exe cache get` initially encountered tar's inability to restore an
archive's original owner. The original leantar archive was extracted locally with
`--no-same-owner`. Cache retrieval then used the 35 Mathlib roots in the required module
closure, downloading and unpacking their 967 dependencies, with these additional cache-only
environment settings:

```sh
MATHLIB_CACHE_DIR=/workspace/scratch/9287e0d90bc1/runtime/cache
TAR_OPTIONS=--no-same-owner
```

No `lake build` command was directly issued. **Runtime procedure escalation E2:** the explicitly
requested `lake exe cache get` utility internally invokes
`lake -v build proofwidgets:release` to fetch its cloud release (and
`lake -v build --no-build proofwidgets:release` to validate an existing release).
Consequently this report cannot attest that no Lake `build` subcommand occurred anywhere
in the cache operation's process tree. No TCSlib project build was run, and the cache
utility was not modified. Every proof, probe and module check used
`scripts/lean_check_tree.sh`.

The execution service disconnected during module 15 of the final sweep, after 14 modules
had passed. The check runner stopped without a result for that module. The sweep was
resumed at module 15, retaining the first 14 successful checks, with the interruption
recorded in the final log. Every module still receives a fresh successful check; none is
skipped. The final source was unchanged during this replay.

Module 41 then failed with OS error 28 (`no space left on device`). Its full failed
attempt is quoted in full in this report. The successful
replay portion was preserved through module 40, and module 41 was rerun after removing
this task's disposable `.ltar` cache archives and generated `.c`, `.ilean`, `.trace` and
hash/object cache outputs, then the completed cache-fetch executable and its temporary
copy (290 MiB). Required dependency oleans and interpreter IR were retained. Disk space
was available again (3.5 GiB at retry); no other workspace was cleaned or modified.
The final success and admission counts below refer to the successful replay, not to the
preserved failed attempt.


### Storage-exhaustion recovery

Disk exhaustion recurred during the first retry. Generated dependency artifacts were
copied byte for byte to `/dev/shm/g4-cont1-9287e0d90bc1/`, with each SHA-256 checked before
an atomic symlink replacement. The relocation stopped when the disk could no longer
allocate another symlink; all completed replacements retained identical contents.
Generated widget JavaScript, future modules' bootstrap oleans (modules 42–80), and
completed scratch-copy oleans were also removed. Required dependency artifacts were
preserved; the future TCSlib outputs are regenerated by the replay.

The still-running disk-bound retry was cancelled (exit 130) after renewed exhaustion.
The successful outputs through module 40 were copied to shared memory. The remaining
checks use the unmodified prescribed check script with these additional supported settings:

```sh
TCSLIB_OLEANS=/dev/shm/g4-cont1-checks/oleans
TMPDIR=/dev/shm/g4-cont1-checks/tmp
```

A first shared-memory attempt found a missing `ImportGraph.Imports` artifact at its
original path. The previously verified dependency copies were restored into the shared-memory
import tree, preserving their bytes, and module 41 was retried. That failed attempt is
quoted below alongside the disk failure. A second attempt exposed a partial Aesop
namespace in the new import root; the complete dependency trees were then copied into
that root, again with byte equality checked, before retrying.

The final source and pinned toolchain are unchanged. Logs and archive staging are also
kept in shared memory so they can be completed despite the full disk. No other workspace
was modified. The complete first disk-failed attempt is quoted below; the cancelled
retry did not return a Lean check result.

After 54 successful replay checks, the unfinished module-55 attempt was stopped
without a result to schedule the remaining 26 modules concurrently (at most four).
Each starts only after every imported TCSlib module has passed; each still runs the
unmodified prescribed check script and produces a fresh olean. The log concatenates
these results in the original order. The bootstrap and both duplication screens remain
sequential. No source change accompanied this scheduling change.

## REPORT.md checklist

- [x] The phase reached; the base hash and the ancestor check.
- [x] The four re-pointed helpers, each with the lemmas it now cites; every other changed or
      removed `zr_` helper.
- [x] Every new declaration with its role; the bridges as recommended or restated; any further
      leaf with its reason; the flagged appendices.
- [x] The scratch layout you used, and the walk convention as applied.
- [x] Promotion candidates and escalations, or "none".
- [x] Rule 10: the declarations cited outside your file, and the probe re-run; a grep of your diff
      for `unfold`, `delta`, `simp only [` and `rfl` on another file's definition, each hit
      explained. Rule 11: a grep of your diff for the six R3 rows.
- [x] Duplication: both v3 screens, every new pair justified, "new copies: none".
- [x] File size; the final sweep tail; the axiom prints; the lint line. The diff touches only your
      owned regions.

## Known pitfalls at this pin (hard-won)

- **Two blanks in a row mark the layout's end; one blank is a separator.** The home is the only
  one-cell field: every zone has `cap ≥ 2`. `zoneStart 0 = 2`, so the separators around home are
  at `±1`.
- **Inner packing:** stored cells sit at each zone's inner end, and `⊠` (`none` in a slot) fills the
  rest.
  - A zone is empty on a track exactly when its innermost slot is `⊠`, and full exactly when its
    outermost slot is occupied (the partial's `zr_inner_empty_iff`, `zr_outer_full_iff`).
  - A stored **virtual blank** is `some none`, not `⊠`.
- **The left side reads reversed** (`zonedTape_left_word`): the left zone `i`'s inner end is at
  `-zoneStart i`, its outer end at `-(zoneStart i + cap_i - 1)`. A rightward mapped copy writes
  from the outer end.
- **The mapped copy writes `merge (old destination cell) (extract source cell)`** and returns both
  heads (`2|w| + 2` steps). The walk moves `|w| + 1` (the convention above).
- **Contracts fix `Γ : Type`;** `ZoneSym k` is one. A `Contract`'s cut includes time `0`, so an
  entry is never an exit.
- **`Round.iterate`** takes a round-time function on configurations and a round hypothesis per
  orbit point; the level can be read off the configuration. Its round `0` is the start
  (`roundOrbit_zero`), and each next round starts where the last ended (`roundOrbit_succ`).
  `RoundContract`'s orbit lemmas fix one index.
- **`Contract.ofSegment`** wants each segment's relation to be exactly the `HeadBox` of the `lo`/`hi`
  you give it: weaken a composed segment's relation by `Segment.mono`, using `headBox_iff`.
- `Contract.inPhase`'s endpoint is a `Cfg.bindState`: read its fields by `Cfg.bindState_state` and
  the other four.
- `omega` with products and powers as atoms (`ring` first). `zoneStart_eq : zoneStart i =
  2^(i+1) + i`, `zoneStart_succ` and `zoneCapacity_eq : zoneCapacity i = 2 * 2^i` are the
  arithmetic. The linter needs a literal "Proof sketch" before every `sorry` (partial only).

The checked boxes mean the requested reporting is supplied. They do not mean the two
machine-row proofs are complete.

## Delivery revision and validation

Final commit: `66765b0c7f0a52ef9352233dd4e99e64ce33ca7b`. Its sole parent is the required base. The patch series
has one patch; applying it to a temporary index at the base reproduces the final commit's
complete tree. The bundle passes `git bundle verify` and has exactly one prerequisite,
`94b986d4db7167ab2a8b20d38d4385f11e60be0e`. The tracked worktree is clean.

| Gate | Result |
|---|---|
| Bootstrap | 80/80 modules, zero errors; the 35 named baseline admissions match exactly |
| Final sweep | 80/80 modules, zero errors; the same 35 named admissions, including the two owned targets |
| Owned file | Exactly two original target warnings; no non-sorry warning |
| Other 79 modules | 33 baseline admission warnings; all other warning lines match the bootstrap byte for byte |
| Extended import probe | 658 checks: the original 338 plus 320 additional dependency names; zero errors and zero warnings |
| Axioms | Both targets and all 31 private declarations printed; every private is within the allowed three axioms |
| Style lint | `style_lint: 0 FAIL, 32 WARN over 37 files` (same as base) |
| File size | 571 → 860 lines; 18 → 18 public declarations; 18 → 31 private declarations |
| Diff scope | Only the owned home and two allowed appendices; all frozen regions byte-identical |
| Added line width | Maximum 99 characters; none above 100 |
| Imports and R3 rows | Imports unchanged; no added prohibited R3 citation |

The pre-existing style warnings are retained; there is no new lint warning. The final log
contains the raw 80-module sweep followed by the import-probe output, lint, scope checks,
admission comparison, screen comparison and Git-package verification.

### Base admission inventory and final difference

The named baseline was recorded before proof edits. The bootstrap and final sweep both
match this list exactly. **Difference: none.** Only its two owned rows remain open here;
the other 33 admissions were not modified.

```text
TuringMachine/Simulation: 1: branchTM_spaceUsed
TuringMachine/Composition: 3: idTM_computes, ifEqTM_computes, condTM_computes_iff
TuringMachine/Build/Wrappers: 2: timedCondTM_computes, timedCondTM_spaceUsed
TuringMachine/Build/Loop: 5: loopHostTM_contracts, loopHostTM_decides, loopHostTM_finds, loopHostTM_spaceUsed_le_budget, emitLoopTM_computes
TuringMachine/Encoding: 1: pairDiagTM_computes
ClassP/TimeConstructible: 2: _root_.Turing.FinTM.lengthBitsTM_computes, _root_.Turing.FinTM.lengthBitsTM_spaceUsed
TuringMachine/Build/NDHost: 1: ndWriterTM_run_block
TuringMachine/Build/Primitives: 3: polyUnaryTM_spaceUsed, unaryTokenTM_computes, appendBitTM_computes
TuringMachine/Build/ZoneRebalance: 2: exists_zoneRebalanceTM, exists_zoneExtendTM
TuringMachine/Build/InputWindow: 1: exists_inputWindowCopyTM
TuringMachine/Build/RecordTable: 4: exists_tableFindTM, exists_tableAppendTM, exists_recordValidTM, exists_recordNextTM
TuringMachine/CodeSimulator: 2: exists_canonGrammarStage [private], exists_uniformSimulator
TuringMachine/NDCodeSimulator: 2: exists_replayCanonizer, exists_ndInterpreterCore
TuringMachine/Build/InputDevice: 3: exists_rulerTestTM, exists_rulerDeviceTM, exists_rulerHostTM
TuringMachine/UniversalK: 3: exists_selfStartupTMK, exists_selfUniversalK, universalK
TOTAL 35
```

### Final sweep tail

```text
Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
EXIT 0
[78/80] TCSlib/Complexity/TuringMachine/UniversalK
TCSlib/Complexity/TuringMachine/UniversalK.lean:188:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/UniversalK.lean:233:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/UniversalK.lean:271:8: warning: declaration uses 'sorry'
EXIT 0
[79/80] TCSlib/Complexity/TuringMachine/SelfUniversal
EXIT 0
[80/80] TCSlib/Complexity/TuringMachine
EXIT 0
PASS 80 modules; dependency-ordered parallel remainder 828.1 seconds; 54 prior successful checks retained
```

### Axiom prints and admission walks

The scratch module is the final source with an additional Lean metaprogramming import
and appended diagnostics. Production imports are unchanged. All 31 private declarations
are printed, which includes all four changed and all 13 new helpers. The walk follows
constant dependencies and lists declarations that directly use `sorryAx`; each target
has only itself in that list.

```text
'Turing.exists_zoneExtendTM' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Turing.exists_zoneRebalanceTM' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'_private.«.lake».G4Axioms.0.Turing.zr_zonePos' depends on axioms: [propext]
'_private.«.lake».G4Axioms.0.Turing.zr_read_slot' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private.«.lake».G4Axioms.0.Turing.zr_capacity_pos' depends on axioms: [propext]
'_private.«.lake».G4Axioms.0.Turing.zr_slot_empty_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private.«.lake».G4Axioms.0.Turing.zr_inner_empty_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private.«.lake».G4Axioms.0.Turing.zr_outer_full_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private.«.lake».G4Axioms.0.Turing.zr_room_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private.«.lake».G4Axioms.0.Turing.zr_scan_index' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private.«.lake».G4Axioms.0.Turing.zr_scan_short' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private.«.lake».G4Axioms.0.Turing.zr_ruler_length' depends on axioms: [propext, Quot.sound]
'_private.«.lake».G4Axioms.0.Turing.zr_extent_cost' depends on axioms: [propext, Quot.sound]
'_private.«.lake».G4Axioms.0.Turing.zr_mirror_tape' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private.«.lake».G4Axioms.0.Turing.zr_extend_cell' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private.«.lake».G4Axioms.0.Turing.zr_ruler_tail' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private.«.lake».G4Axioms.0.Turing.zr_cellTM' does not depend on any axioms
'_private.«.lake».G4Axioms.0.Turing.zr_cellPost' depends on axioms: [propext]
'_private.«.lake».G4Axioms.0.Turing.zr_cell_step' depends on axioms: [propext, Quot.sound]
'_private.«.lake».G4Axioms.0.Turing.zr_cellContract' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private.«.lake».G4Axioms.0.Turing.zr_fieldsTape_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private.«.lake».G4Axioms.0.Turing.zr_right_offset' depends on axioms: [propext, Quot.sound]
'_private.«.lake».G4Axioms.0.Turing.zr_zonedTape_right_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.«.lake».G4Axioms.0.Turing.zr_left_offset' depends on axioms: [propext, Quot.sound]
'_private.«.lake».G4Axioms.0.Turing.zr_zonedTape_left_fields' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private.«.lake».G4Axioms.0.Turing.zr_zoneCells_ne_nil' depends on axioms: [propext]
'_private.«.lake».G4Axioms.0.Turing.zr_seekEnd_pre' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private.«.lake».G4Axioms.0.Turing.zr_seekStart_pre' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private.«.lake».G4Axioms.0.Turing.zr_left_two_walks' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private.«.lake».G4Axioms.0.Turing.zr_shift_commute' depends on axioms: [propext, Quot.sound]
'_private.«.lake».G4Axioms.0.Turing.zr_inPass_out' depends on axioms: [propext, Quot.sound]
'_private.«.lake».G4Axioms.0.Turing.zr_pair_pass' depends on axioms: [propext, Quot.sound]
'_private.«.lake».G4Axioms.0.Turing.zr_cascade_passes' depends on axioms: [propext, Quot.sound]
Turing.exists_zoneExtendTM: direct sorryAx users in closure: [Turing.exists_zoneExtendTM]
Turing.exists_zoneRebalanceTM: direct sorryAx users in closure: [Turing.exists_zoneRebalanceTM]
```

## Rule 10 and rule 11 review

The added-line diff grep below contains no `unfold` or `delta`. Every `rfl` hit is an
equality-substitution pattern, not a proof that unfolds an external definition. In `simp only`,
`fs` is a proof-local list; `hcell`, `hl` and `hr` are local proved equations; and
`zr_pair_pass` is this file's proved private lemma. Every other named rewrite in these hits is
a published Lean/Mathlib or TCSlib lemma. Thus these categories account for every hit.

```lean
  simp only [hcell, Option.map_some, zoneSlotOf_inr]
  simp only [zoneCapacity_eq, Nat.mul_comm]
  rcases lt_trichotomy c 0 with hn | rfl | hp
    simp only [zoneCellAt_eq, ZoneContents.words_false, ZoneContents.swap_left,
  · simp only [neg_zero, zonedTape_zero, ZoneContents.swap_home]
    simp only [neg_neg, zoneCellAt_eq, ZoneContents.words_true, ZoneContents.swap_right,
    rw [fieldOffset_succ _ (i + 1) (by simp only [List.length_cons, List.length_ofFn]; omega)]
    simp only [List.getElem_cons_succ, List.getElem_ofFn, zoneCells_length]
  have hlen : fs.length = ℓ + 1 := by simp only [fs, List.length_cons, List.length_ofFn]
      simp only [fs, List.getElem_cons_zero, List.length_singleton] at hq' ⊢
      rcases hcases with rfl | rfl
      · simp only [Nat.cast_zero, zero_add, zonedTape_zero]
      simp only [fs, List.getElem_cons_succ, List.getElem_ofFn, zoneCells_length] at hq' ⊢
    have hjoin := length_joinFields_add_one fs (by simp only [fs, ne_eq, List.cons_ne_nil,
    rw [fieldOffset_succ _ j (by simp only [List.length_ofFn]; omega)]
    simp only [List.getElem_ofFn, List.length_reverse, zoneCells_length, Fin.val_rev]
    simp only [fs, List.getElem_ofFn, List.length_reverse, zoneCells_length] at hq' ⊢
    simp only [List.mem_cons, List.mem_ofFn] at hu
    rcases hu with rfl | ⟨i, rfl⟩
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hu
    simp only [List.length_ofFn] at he ⊢
  simp only [Nat.sub_self] at ht
    simp only [zoneShiftIn_left, if_true]
    simp only [zoneShiftOut_right, Bool.false_eq_true, if_false]
  · simp only [zoneShiftIn_home, zoneShiftOut_home]
    simp only [zoneShiftIn_left, zoneShiftOut_left, Bool.false_eq_true, if_false, if_true, hl]
    simp only [zoneShiftIn_right, zoneShiftOut_right, Bool.false_eq_true, if_false, if_true, hr]
  | nil => simp only [List.foldl_nil]
  | nil => simp only [List.foldl_nil]
    simp only [List.foldl_cons]
  simp only [zr_pair_pass]
```

The six prohibited R3 names have **zero added-line hits**. Direct dependency extraction
from all private helpers finds **no external private declaration**, including Catalog privates.
No new TCSlib or Mathlib import was added.

The inventory below lists all 381 direct external kernel dependencies of the 31 private
helpers, including inherited helpers, their types, implicit instances and core proof constants.
The 338-name published probe is extended by its 320 additional names, for 658 checks.
The probe is run through the same required check script.

```text
AddCancelCommMonoid.toAddCancelMonoid
AddCancelMonoid.toAddRightCancelMonoid
AddCommGroup.toDivisionAddCommMonoid
AddCommMagma.toAdd
AddCommMonoidWithOne.toAddMonoidWithOne
AddCommSemigroup.toAddCommMagma
AddGroup.toSubNegMonoid
AddGroup.toSubtractionMonoid
AddGroupWithOne.toAddGroup
AddGroupWithOne.toAddMonoidWithOne
AddMonoid.toAddSemigroup
AddMonoid.toAddZeroClass
AddMonoidWithOne.toAddMonoid
AddMonoidWithOne.toNatCast
AddMonoidWithOne.toOne
AddRightCancelMonoid.toAddRightCancelSemigroup
AddRightCancelSemigroup.toIsRightCancelAdd
AddSemigroup.toAdd
AddZero.toAdd
AddZero.toZero
AddZeroClass.toAddZero
And
And.intro
And.left
And.right
Bool
Bool.casesOn
Bool.false
Bool.false_eq_true
Bool.true
Classical.byContradiction
CommRing.toNonUnitalCommRing
Decidable.byContradiction
Decidable.decide
Distrib.leftDistribClass
Distrib.toMul
Eq
Eq.mp
Eq.mpr
Eq.ndrec
Eq.rec
Eq.refl
Eq.symm
Eq.trans
Exists
Exists.casesOn
False
False.elim
Fin
Fin.instOfNat
Fin.mk
Fin.rev
Fin.val
Fin.val_rev
Function.update
GetElem.getElem
GetElem?.getElem?
HAdd.hAdd
HMul.hMul
HPow.hPow
HSub.hSub
HasDistribNeg.toInvolutiveNeg
Iff
Iff.mp
Iff.mpr
Iff.rfl
Int
Int.decLe
Int.decLt
Int.instAdd
Int.instAddCommGroup
Int.instAddGroup
Int.instAddLeftMono
Int.instAddMonoid
Int.instCommRing
Int.instDecidableEq
Int.instDistrib
Int.instLEInt
Int.instLTInt
Int.instLinearOrder
Int.instMax
Int.instMin
Int.instMul
Int.instNegInt
Int.instRing
Int.instSemiring
Int.instSub
Int.ofNat
Int.toNat
InvolutiveNeg.toNeg
IsOrderedAddMonoid.toAddLeftMono
IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT
LE.le
LT.lt
Lattice.toSemilatticeInf
LinearOrder.toPartialOrder
List
List.casesOn
List.cons
List.cons_ne_nil
List.foldl
List.foldl_cons
List.getElem?_eq_none_iff
List.getElem_ofFn
List.getElem_ofFn._proof_1
List.instGetElem?NatLtLength
List.instGetElemNatLtLength
List.instMembership
List.length
List.length_ofFn
List.length_reverse
List.mem_ofFn
List.ne_nil_of_length_pos
List.nil
List.ofFn
List.range
List.rec
List.reverse
List.reverse_ne_nil_iff
List.tail
Mathlib.Meta.NormNum.IsInt.to_isNat
Mathlib.Meta.NormNum.IsNat.to_eq
Mathlib.Meta.NormNum.IsNat.to_isInt
Mathlib.Meta.NormNum.instAddMonoidWithOne
Mathlib.Meta.NormNum.isInt_sub
Mathlib.Meta.NormNum.isNat_add
Mathlib.Meta.NormNum.isNat_ofNat
Mathlib.Meta.NormNum.isNat_pow
Mathlib.Meta.NormNum.natPow_one
Max.max
Membership.mem
Min.min
Monoid.toMulOneClass
Monoid.toNatPow
MonoidWithZero.toMonoid
MulOne.toMul
MulOne.toOne
MulOneClass.toMulOne
MulZeroClass.toZero
MulZeroOneClass.toMulOneClass
Nat
Nat.add_sub_cancel_left
Nat.casesAuxOn
Nat.cast
Nat.cast_add
Nat.cast_mul
Nat.cast_one
Nat.cast_pow
Nat.cast_zero
Nat.decLe
Nat.decLt
Nat.instAddCancelCommMonoid
Nat.instAddCommMonoid
Nat.instAddCommSemigroup
Nat.instAddMonoid
Nat.instAddMonoidWithOne
Nat.instAtLeastTwoHAddOfNat
Nat.instIsOrderedAddMonoid
Nat.instLinearOrder
Nat.instMonoid
Nat.instNeZeroSucc
Nat.instPartialOrder
Nat.instPreorder
Nat.instSemiring
Nat.lt_of_succ_lt_succ
Nat.lt_two_pow_self
Nat.mul_comm
Nat.mul_pos
Nat.recAux
Nat.sub_self
Nat.sub_zero
Nat.two_pow_pos
Nat.zero_add
Ne
Neg.neg
NegZeroClass.toNeg
NegZeroClass.toZero
NonAssocSemiring.toAddCommMonoidWithOne
NonAssocSemiring.toMulZeroOneClass
NonAssocSemiring.toNonUnitalNonAssocSemiring
NonUnitalCommRing.toNonUnitalNonAssocCommRing
NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring
NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing
NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring
NonUnitalNonAssocRing.toHasDistribNeg
NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring
NonUnitalNonAssocSemiring.toDistrib
NonUnitalNonAssocSemiring.toMulZeroClass
Not
OfNat.ofNat
One.toOfNat1
Option
Option.casesOn
Option.map
Option.none
Option.some
Option.some.injEq
Option.some_ne_none
Or
Or.casesOn
PartialOrder.toPreorder
Preorder.toLE
Preorder.toLT
Ring.toAddGroupWithOne
SemilatticeInf.toPartialOrder
Semiring.toMonoidWithZero
Semiring.toNonAssocSemiring
Set
Set.instSingletonSet
Set.range
Sigma.fst
Sigma.mk
Sigma.snd
SignType
SignType.cast
SignType.instZero
Singleton.singleton
SubNegMonoid.toAddMonoid
SubNegMonoid.toNeg
SubNegMonoid.toSub
SubNegZeroMonoid.toNegZeroClass
SubtractionCommMonoid.toSubtractionMonoid
SubtractionMonoid.toSubNegZeroMonoid
Sum.inr
Trans.trans
True
True.intro
Turing.Action
Turing.Cfg
Turing.Cfg.inputPos
Turing.Cfg.inputSymbol
Turing.Cfg.mk
Turing.Cfg.output
Turing.Cfg.state
Turing.Cfg.workTapePos
Turing.Cfg.workTapeSymbols
Turing.Cfg.workTapes
Turing.Contract
Turing.Contract.mk
Turing.Contract.pre
Turing.FinTM.bufferTape
Turing.FinTM.bufferTape_nat
Turing.MultiTapeTM
Turing.MultiTapeTM.mk
Turing.MultiTapeTM.step
Turing.MultiTapeTM.tr
Turing.SeekPhase
Turing.SeekPhase.done
Turing.SeekPhase.run
Turing.ZoneCell
Turing.ZoneContents
Turing.ZoneContents.ext'
Turing.ZoneContents.extend
Turing.ZoneContents.home
Turing.ZoneContents.left
Turing.ZoneContents.right
Turing.ZoneContents.swap
Turing.ZoneContents.words
Turing.ZoneContents.words_le
Turing.ZoneSym
Turing.fieldOffset
Turing.fieldOffset_cons_succ
Turing.fieldOffset_succ
Turing.fieldOffset_zero
Turing.fieldsTape
Turing.fieldsTape_field
Turing.fieldsTape_of_length_le
Turing.fieldsTape_of_neg
Turing.inputMoveAction
Turing.joinFields
Turing.length_joinFields_add_one
Turing.moveInputPos
Turing.moveInputPos_zero
Turing.seekEndTM
Turing.seekEndTM_contract
Turing.seekEndTM_contract_pre
Turing.seekStartTM
Turing.seekStartTM_contract
Turing.seekStartTM_contract_pre
Turing.step_of_tapeAction_move
Turing.step_of_tapeAction_write
Turing.tapeAction
Turing.zoneCapacity
Turing.zoneCapacity_eq
Turing.zoneCascadeRight
Turing.zoneCascadeRight_eq
Turing.zoneCellAt
Turing.zoneCells
Turing.zoneCells_length
Turing.zoneMove
Turing.zoneOwner
Turing.zoneRebalance
Turing.zoneRebalance_of_le
Turing.zoneShiftIn
Turing.zoneShiftInW
Turing.zoneShiftIndex
Turing.zoneShiftIndex_eq
Turing.zoneShiftIndex_eq_length_iff
Turing.zoneShiftOut
Turing.zoneShiftOutW
Turing.zoneSlotOf
Turing.zoneStart
Turing.zoneStart_eq
Turing.zoneStart_succ
Turing.zoneStepPair
Turing.zoneStepPair_eq
Turing.zonedTape
Turing.zonedTape_blank_outside
Turing.zonedTape_extend
Turing.zonedTape_left
Turing.zonedTape_left_word
Turing.zonedTape_of_neg
Turing.zonedTape_of_pos
Turing.zonedTape_right
Turing.zonedTape_right_sep
Turing.zonedTape_right_word
Turing.zonedTape_zero
Unit
Zero.toOfNat0
abs
abs_neg
abs_of_nonneg
abs_of_nonpos
add_zero
congr
congrArg
congrFun
contravariant_lt_of_covariant_le
contravariant_swap_add_of_contravariant_add
covariant_swap_add_of_covariant_add
dite
eq_self
eq_true
funext
id
if_false
if_pos
if_true
iff_self
instAddNat
instDecidableAnd
instDecidableEqBool
instDecidableEqFin
instDecidableEqNat
instDecidableFalse
instDecidableIff
instDecidableNot
instDecidableOr
instDecidableTrue
instHAdd
instHMul
instHPow
instHSub
instLENat
instLTNat
instLatticeInt
instMulNat
instNatCastInt
instOfNat
instOfNatAtLeastTwo
instOfNatNat
instSubNat
instTransEq
ite
ite_congr
le_rfl
lt_trichotomy
mul_add
mul_le_mul_iff_right._simp_4
mul_one
ne_eq
neg_neg
neg_zero
not_false_eq_true
of_decide_eq_true
of_eq_true
pow_succ
propext
rfl
zero_add
zero_sub
```

## Duplication review

Both v3 screens ran sequentially under `nice -n 10` over the exact ten-file population.
The before output is byte-identical to the supplied baseline. After the four replacements
and 13 new helpers, the declaration count is 808, with 439 directed pairs and 127,994
reproduced characters. There are no removed baseline pairs and no new cross-file pair.

**new copies: none.** The two new directed in-file screen hits are justified individually:

| New directed pair | Screen result | Disposition |
|---|---|---|
| `zr_inPass_out` → `zr_pair_pass` | 92/149 = 62% | Shared list-induction syntax; the first proves commutation of one left shift with a right pass, while the second uses that lemma to reorder a pair list. |
| `zr_pair_pass` → `zr_inPass_out` | 92/127 = 72% | The reverse direction of the same syntax match; it does not repeat the mathematical commutation proof, which is cited through the shared helper. |

The screen's single shared whitespace-normalized tile is exactly:

```text
byinductionisgeneralizingzwith|nil=>simponly[List.foldl_nil]|consiisih=>rw[List.foldl_cons,z
```

Neither hit reaches 90%. The shared mathematical arguments occur once: the layout
comparison in `zr_fieldsTape_eq`, the shift commutation in `zr_shift_commute`, and the
pair reordering in `zr_pair_pass`. No copied private host or Catalog/RecordTable proof
has been added. Both complete screen outputs follow, without filtering.

### Screen before (complete)

```text
declarations screened: 795; copy pairs (target reproduces >= half of source): 437; reproduced text: 127,810 chars
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_space_of_time  reproduces  Simulation.lean::ComputesInTime.spaceUsed_le: 713/713 = 100%
   Simulation.lean::ComputesInTime.spaceUsed_le  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_space_of_time: 713/713 = 100%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_catalogRewind  reproduces  Simulation.lean::timed_rewind: 435/435 = 100%
   Simulation.lean::timed_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_catalogRewind: 435/435 = 100%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_finSumEquiv  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_mapSumEquiv: 362/362 = 100%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_mapSumEquiv  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_finSumEquiv: 362/362 = 100%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::step_of_tapeAction_write  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::step_of_tapeAction_move: 167/167 = 100%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::step_of_tapeAction_move  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::step_of_tapeAction_write: 167/167 = 100%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamReleaseTM_step_inr  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_right: 135/135 = 100%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_right  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamReleaseTM_step_inr: 135/135 = 100%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::seekEndTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::skipTM: 129/129 = 100%
   TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean::branch_positive  reproduces  TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean::seq_positive: 62/62 = 100%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_payload_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_fuel_rewind: 1304/1306 = 100%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loop_rewind_bounded  reproduces  Simulation.lean::rewind_from_any: 465/466 = 100%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::transferTM_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::Cfg.ofWords_transfer_endpoint: 478/480 = 100%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_fuel_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_payload_rewind: 1304/1314 = 99%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::copyTM_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::Cfg.ofWords_copy_endpoint: 228/230 = 99%
   Zone.lean::zoneTrackTape_rebalance_right  reproduces  Zone.lean::zoneSide_rebalance_right: 266/269 = 99%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::Cfg.ofWords_transfer_endpoint  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::Cfg.ofWords_copy_endpoint: 227/230 = 99%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::transferTM_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::Cfg.ofWords_copy_endpoint: 225/230 = 98%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_left  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamReleaseTM_step_inr: 132/135 = 98%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_left  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_right: 132/135 = 98%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_lenSuffix_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_lenParse_first: 312/320 = 98%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_pairSnd_spaceUsed  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_pairConcat_spaceUsed: 305/314 = 97%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_pairFst_spaceUsed  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_pairConcat_spaceUsed: 305/314 = 97%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_scanTrues_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_scanStep_right: 159/164 = 97%
   Zone.lean::zoneShiftOut  reproduces  Zone.lean::zoneShiftIn: 314/324 = 97%
   Zone.lean::zoneSide_rebalance_right  reproduces  Zone.lean::zoneTrackTape_rebalance_right: 266/275 = 97%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_pairConcat_spaceUsed  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_pairSnd_spaceUsed: 305/317 = 96%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_pairConcat_spaceUsed  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_pairFst_spaceUsed: 305/317 = 96%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::transferTM_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::copyTM_run: 388/404 = 96%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::transferMapTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::copyMapTM: 478/498 = 96%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::clearTM_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::Cfg.ofWords_copy_endpoint: 220/230 = 96%
   Zone.lean::zoneShiftIn  reproduces  Zone.lean::zoneShiftOut: 314/329 = 95%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_extract_replay  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_rawStrip_replay: 393/412 = 95%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_anchor_return  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_call_run: 299/315 = 95%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopCall_reframe  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopCall_frame: 500/527 = 95%
   ZoneTape.lean::zoneOwner_sep  reproduces  ZoneTape.lean::zoneOwner_beyond: 105/111 = 95%
   Basic.lean::RoundContract  reproduces  Basic.lean::ReturnContract: 412/436 = 94%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_incFixed_computes  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_scanStep_right: 154/164 = 94%
   ZoneTape.lean::zonedTape_left  reproduces  ZoneTape.lean::zonedTape_right: 171/183 = 93%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_pairDup_double  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_scanStep_right: 152/164 = 93%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_pairSnd_spaceUsed  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_pairFst_spaceUsed: 293/317 = 92%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_pairFst_spaceUsed  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_pairSnd_spaceUsed: 293/317 = 92%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_branch_space  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::catalog_space_one: 115/125 = 92%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_map_block  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_map_move: 331/362 = 91%
   Simulation.lean::rewind_heads  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_catalogRewind: 395/435 = 91%
   Simulation.lean::rewind_heads  reproduces  Simulation.lean::timed_rewind: 395/435 = 91%
   Simulation.lean::rewind_from_any  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loop_rewind_bounded: 465/514 = 90%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitEmbed_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamReleaseTM_step_inr: 122/135 = 90%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitEmbed_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_right: 122/135 = 90%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::copyMapTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::clearTM: 369/409 = 90%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_map_suffix  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_map_move: 326/362 = 90%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::incrementTM_run_succ_ofCfg  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::incrementTM_run_overflow_ofCfg: 617/686 = 90%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::copyMapTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::transferMapTM: 478/533 = 90%
   ZoneTape.lean::zonedTape_right  reproduces  ZoneTape.lean::zonedTape_left: 171/191 = 90%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_halt_return  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_call_run: 279/315 = 89%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::copyTM_spaceUsedByTape  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::transferTM_spaceUsedByTape: 625/713 = 88%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::copyTM_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::clearTM_run: 336/385 = 87%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_extract_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_rawStrip_rewind: 632/725 = 87%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_borrow_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopBorrow_run: 414/476 = 87%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_map_backB  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_map_backA: 806/927 = 87%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_body_capture  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_fuel_capture: 96/111 = 86%
   TCSlib/Complexity/TuringMachine/Build/Contract/Catalog.lean::transferMapTM_contract  reproduces  TCSlib/Complexity/TuringMachine/Build/Contract/Catalog.lean::copyMapTM_contract: 120/139 = 86%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::transferTM_spaceUsedByTape  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::copyTM_spaceUsedByTape: 625/727 = 86%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitRestore_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitPrepare_rewind: 664/776 = 86%
   Basic.lean::Cfg.SameOutside.keep_blank  reproduces  Basic.lean::endpoint_not_mem: 97/114 = 85%
   TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean::seq_positive  reproduces  TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean::branch_positive: 62/73 = 85%
   Basic.lean::safeSegment_iff  reproduces  Basic.lean::segment_iff: 84/99 = 85%
   Basic.lean::time_box  reproduces  Basic.lean::time_envelope: 123/146 = 84%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::transferMapTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::clearTM: 344/409 = 84%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::seekStartTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::seekEndTM: 173/206 = 84%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_call_heads  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_fuel_heads: 515/615 = 84%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_fuel_return  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_fuel_rewind: 1092/1306 = 84%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::clearTM_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::copyTM_run: 336/404 = 83%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_fuel_return  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_payload_rewind: 1092/1314 = 83%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_map_backA  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_map_backB: 806/975 = 83%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_rawStrip_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_extract_rewind: 632/767 = 82%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_fuel_capture  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_body_capture: 96/117 = 82%
   Basic.lean::hullLo  reproduces  Basic.lean::hullHi: 114/139 = 82%
   Basic.lean::hullHi  reproduces  Basic.lean::hullLo: 114/139 = 82%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitPrepare_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitRestore_rewind: 664/814 = 82%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::transferTM_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::clearTM_run: 314/385 = 82%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_sum_add  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_map_sum: 153/188 = 81%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_map_sum  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_sum_add: 153/188 = 81%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_fuel_return  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_borrow_rewind: 1077/1329 = 81%
   Simulation.lean::rightCfg_step  reproduces  Simulation.lean::leftCfg_step: 306/378 = 81%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::step_of_tapeAction_write  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::step_of_inputMoveAction: 68/84 = 81%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::step_of_tapeAction_move  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::step_of_inputMoveAction: 68/84 = 81%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_counter_count_space  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_counter_count: 363/452 = 80%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::seekStartTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::skipBackTM: 162/202 = 80%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_payload_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_fuel_return: 1092/1366 = 80%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_fuel_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_fuel_return: 1092/1366 = 80%
   Simulation.lean::leftCfg_step  reproduces  Simulation.lean::rightCfg_step: 306/384 = 80%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_extract_suffix  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_extract_first: 238/300 = 79%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::skipBackTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::skipTM: 102/129 = 79%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_call_heads  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopCall_heads: 520/658 = 79%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitRestore_scan  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitPrepare_scan: 526/666 = 79%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_borrow_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_fuel_return: 1077/1366 = 79%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_branch_space  reproduces  Simulation.lean::branchTM_computes: 632/802 = 79%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::transferTM_run_ofCfg  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::copyTM_run_ofCfg: 89/113 = 79%
   Simulation.lean::bufferedFirstCfg_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_mapSetup_run: 128/163 = 79%
   ZoneTape.lean::zonedTape_left_sep  reproduces  ZoneTape.lean::zonedTape_right_sep: 124/158 = 78%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::seekStartTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::skipTM: 101/129 = 78%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::incrementTM_run_succ  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::incrementTM_run_overflow: 383/491 = 78%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_loop_prepare  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_prepare: 1165/1499 = 78%
   Basic.lean::endpoint_not_mem  reproduces  Basic.lean::traj_iff: 80/103 = 78%
   Basic.lean::Frames.trans  reproduces  Basic.lean::traj_iff: 80/103 = 78%
   Basic.lean::Cfg.SameOutside.keep_blank  reproduces  Basic.lean::traj_iff: 80/103 = 78%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::incrementTM_run_overflow  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::clearTM_run: 299/385 = 78%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::compareTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::incrementTM: 408/526 = 78%
   ZoneTape.lean::zonedTape_right_sep  reproduces  ZoneTape.lean::zonedTape_left_sep: 124/162 = 77%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_counterTape_write  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopBuffer_write: 311/408 = 76%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_scanCopy_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_scanStep_right: 125/164 = 76%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopBorrow_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_borrow_run: 414/544 = 76%
   Basic.lean::round_iff  reproduces  Basic.lean::segment_iff: 75/99 = 76%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopBorrow_step  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopReplay_step: 258/341 = 76%
   Simulation.lean::rightCfg_apply  reproduces  Simulation.lean::leftCfg_apply: 142/188 = 76%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamReleaseTM: 148/196 = 76%
   Zone.lean::zoneMoveRight  reproduces  Zone.lean::zoneMoveLeft: 336/445 = 76%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitCount_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_mapSetup_run: 123/163 = 75%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitPrepare_scan  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitPrepare_extra: 356/472 = 75%
   Zone.lean::zoneSide_shiftOutW  reproduces  Zone.lean::zoneSide_shiftInW: 296/394 = 75%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_extract_replay  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_extract_replay_finish: 230/307 = 75%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_runFrom_left  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_mapSetup_run: 122/163 = 75%
   Zone.lean::zoneMoveLeft  reproduces  Zone.lean::zoneMoveRight: 336/449 = 75%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::incrementTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::clearTM: 305/409 = 75%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_runFrom_left  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::catalog_redirect_loop  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_mapSetup_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Simulation.lean::bufferedFirstCfg_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::compareTM_spaceUsedByTape  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::compareTM_run: 286/384 = 74%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_counterInc_potential  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_counterInc_length: 106/143 = 74%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::clearTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::copyMapTM: 369/498 = 74%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_extract_block  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_extract_first: 222/300 = 74%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopCall_heads  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_call_heads: 520/703 = 74%
   Simulation.lean::leftCfg_apply  reproduces  Simulation.lean::rightCfg_apply: 142/192 = 74%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::incrementTM_run_overflow_ofCfg  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::incrementTM_run_succ_ofCfg: 617/839 = 74%
   Basic.lean::segment_iff  reproduces  Basic.lean::round_iff: 75/102 = 74%
   Basic.lean::safeSegment_iff  reproduces  Basic.lean::round_iff: 75/102 = 74%
   Basic.lean::endpoint_not_mem  reproduces  Basic.lean::Cfg.SameOutside.keep_blank: 97/132 = 73%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::incrementTM_run_succ  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::Cfg.ofWords_copy_endpoint: 169/230 = 73%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::incrementTM_run_overflow  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::Cfg.ofWords_copy_endpoint: 169/230 = 73%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loop_find_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_loop_halted_run: 484/659 = 73%
   Simulation.lean::bufferedSecondCfg_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_mapVirtual_run: 190/259 = 73%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopFrame  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopControlAction: 110/150 = 73%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_incFixedTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_pairDupTM: 283/386 = 73%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_fuel_heads  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_call_heads: 515/703 = 73%
   RecordTable.lean::rt_copyState_fintype  reproduces  RecordTable.lean::rt_copyState: 76/104 = 73%
   RecordTable.lean::rt_copyState_decidableEq  reproduces  RecordTable.lean::rt_copyState: 76/104 = 73%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_counterTape_read  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopBuffer_read: 65/89 = 73%
   Simulation.lean::bufferedFirstCfg_step  reproduces  Simulation.lean::bufferedFirstCfg_init: 235/322 = 73%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_catalogPoly_setup  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_catalogPoly_emit: 384/527 = 73%
   Basic.lean::ReturnContract  reproduces  Basic.lean::RoundContract: 412/566 = 73%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_mapSetup_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_runFrom_left: 122/168 = 73%
   Simulation.lean::bufferedFirstCfg_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_runFrom_left: 122/168 = 73%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_anchor_return  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopBody_capture: 270/372 = 73%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitCount_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_mapSetup_heads: 71/98 = 72%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_mapSetup_stationary  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_mapSetup_heads: 71/98 = 72%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_spaceUsedByTape_le_max  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_spaceUsedByTape_le_add: 92/127 = 72%
   Zone.lean::zoneShiftIndex_nonempty  reproduces  Zone.lean::zoneShiftIndex_le: 80/111 = 72%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopBuffer_write  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_counterTape_write: 311/432 = 72%
   Simulation.lean::rightAction  reproduces  Simulation.lean::leftAction: 69/96 = 72%
   Simulation.lean::leftAction  reproduces  Simulation.lean::rightAction: 69/96 = 72%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitRestoreScan  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitPrepareScan: 74/103 = 72%
   Basic.lean::locate  reproduces  Basic.lean::cut: 219/305 = 72%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitRestore_append  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitPrepare_extra: 338/472 = 72%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitCount_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_runFrom_left: 120/168 = 71%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_loop_halted_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loop_find_run: 484/678 = 71%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_borrow  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopBorrow_correct: 261/367 = 71%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_map_setup  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_map_move: 257/362 = 71%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_rawStripTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopReplayTM: 92/130 = 71%
   RecordTable.lean::rt_copyState_decidableEq  reproduces  RecordTable.lean::rt_copyState_fintype: 92/130 = 71%
   Simulation.lean::branchTM_computes  reproduces  Simulation.lean::leftCfg_apply: 133/188 = 71%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_firstReturn  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_run: 151/214 = 71%
   Simulation.lean::branchTM_computes  reproduces  Simulation.lean::rightCfg_apply: 135/192 = 70%
   Simulation.lean::rightCfg_run  reproduces  Simulation.lean::leftCfg_run: 71/101 = 70%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::Cfg.ofWords_transfer_endpoint  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::transferTM_run: 478/680 = 70%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_cond_ledger  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_timed_start: 754/1073 = 70%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitRestoreTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitPrepareTM: 280/399 = 70%
   Basic.lean::traj_iff  reproduces  Basic.lean::endpoint_not_mem: 80/114 = 70%
   Basic.lean::Frames.trans  reproduces  Basic.lean::endpoint_not_mem: 80/114 = 70%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::incrementTM_run_succ  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::clearTM_run: 270/385 = 70%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_extract_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_extract_replay_finish: 215/307 = 70%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_heads_halted  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_heads_join: 72/103 = 70%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopBody_step  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopBody_stop: 245/352 = 70%
   Simulation.lean::bufferedScanCfg_run  reproduces  Simulation.lean::bufferedFirstCfg_init: 224/322 = 70%
   Simulation.lean::bufferedFirstCfg_rewind  reproduces  Simulation.lean::bufferedFirstCfg_init: 224/322 = 70%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_lenParse_block  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_lenParse_first: 222/320 = 69%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::incrementTM_run_overflow  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::copyTM_run: 280/404 = 69%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::catalogIncR  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::catalogCompareR: 63/91 = 69%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_mapVirtual  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_mapCfg: 92/133 = 69%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::catalogIncF  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::catalogIncR: 152/220 = 69%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::copyTM_run_ofCfg  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::transferTM_run_ofCfg: 89/129 = 69%
   Simulation.lean::leftCfg_run  reproduces  Simulation.lean::rightCfg_run: 71/103 = 69%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::seekEndTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::seekStartTM: 173/251 = 69%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitEmbed_cut  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamReleaseTM_step_inr: 93/135 = 69%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitEmbed_cut  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_right: 93/135 = 69%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_incFixed_spaceUsed  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_pairDup_spaceUsed: 74/108 = 69%
   TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean::RoundContract.release  reproduces  TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean::ReturnContract.release: 774/1135 = 68%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_counter_heads  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_counter_computes: 666/977 = 68%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_counterInc_bits  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopValue_bits: 96/141 = 68%
   RecordTable.lean::rt_find_scan_phase  reproduces  RecordTable.lean::rt_find_skip_phase: 344/508 = 68%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_anchor_return  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_halt_return: 342/508 = 67%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_pairDup_spaceUsed  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_incFixed_spaceUsed: 74/110 = 67%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::catalog_transferMap_trace  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::catalog_clear_trace: 1086/1617 = 67%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_rawStrip_replay  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_extract_replay_finish: 206/307 = 67%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_rawStrip_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_rawStrip_replay: 276/412 = 67%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_rawStrip_replay  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_extract_replay: 393/587 = 67%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_mapVirtual_run  reproduces  Simulation.lean::bufferedSecondCfg_run: 190/284 = 67%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_fuel_copy  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_fuel_rewind: 872/1306 = 67%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_extract_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_lenParse_run: 1137/1703 = 67%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::catalogIncR  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::catalogIncF: 152/228 = 67%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::scanResult_fold  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::scanResult_map: 92/138 = 67%
   RecordTable.lean::rt_copyState_fintype  reproduces  RecordTable.lean::rt_copyState_decidableEq: 92/138 = 67%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::incrementTM_run_succ  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::copyTM_run: 269/404 = 67%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_fuel_copy  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_payload_rewind: 874/1314 = 67%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_catalogRewind  reproduces  Simulation.lean::rewind_heads: 395/594 = 66%
   Simulation.lean::timed_rewind  reproduces  Simulation.lean::rewind_heads: 395/594 = 66%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_scanCopy_suffix  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_scanStep_right: 109/164 = 66%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_map_suffix  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_map_first: 232/351 = 66%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitPrepareScan  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitRestoreScan: 74/112 = 66%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_branch_space  reproduces  Simulation.lean::leftCfg_apply: 124/188 = 66%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_incFixedTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitRewindTM: 122/185 = 66%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_branch_space  reproduces  Simulation.lean::rightCfg_apply: 126/192 = 66%
   RecordTable.lean::rt_tailState_decidableEq  reproduces  RecordTable.lean::rt_tailState_fintype: 64/98 = 65%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopReady_call  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopCall_frame: 344/527 = 65%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_poly_space  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_space_radius: 239/367 = 65%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamReleaseTM_step_inr  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitEmbed_run: 122/188 = 65%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_right  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitEmbed_run: 122/188 = 65%
   Simulation.lean::rightCfg  reproduces  Simulation.lean::leftCfg: 84/130 = 65%
   Simulation.lean::leftCfg  reproduces  Simulation.lean::rightCfg: 84/130 = 65%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::skipBackTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::seekStartTM: 162/251 = 65%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::clearTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::transferMapTM: 344/533 = 65%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_timed_read  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_control_heads: 109/169 = 64%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_left  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitEmbed_run: 121/188 = 64%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitEmbed_cut  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitEmbed_run: 121/188 = 64%
   Simulation.lean::bufferedScanCfg_run  reproduces  Simulation.lean::bufferedFirstCfg_rewind: 473/735 = 64%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_catalogPoly_emit  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_catalogPoly_setup: 384/598 = 64%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_counter_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_counter_emit_run: 431/672 = 64%
   Zone.lean::zoneSide_shiftInW  reproduces  Zone.lean::zoneSide_shiftOutW: 296/462 = 64%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_firstReturn: 151/237 = 64%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_extract_suffix  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_scanCopy_suffix: 553/868 = 64%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitBody_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitBody_restore: 333/523 = 64%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitPrepare_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_rawStrip_rewind: 460/725 = 63%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::scanResult_map  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::scanResult_fold: 92/145 = 63%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_pairExtractTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopReplayTM: 82/130 = 63%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_read_heads  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_control_heads: 106/169 = 63%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_pairDupTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitRewindTM: 116/185 = 63%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::incrementTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::compareTM: 408/651 = 63%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::skipTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::seekEndTM: 129/206 = 63%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_pairDup_double  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_scanCopy_run: 311/497 = 63%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopBorrow_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_rawStrip_rewind: 453/725 = 62%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_extract_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_rawStrip_replay: 257/412 = 62%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_rawStrip_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_extract_replay_finish: 191/307 = 62%
   Zone.lean::zoneShiftIndex_nonempty  reproduces  Zone.lean::zoneShiftIndex_empty: 115/185 = 62%
   Basic.lean::RoundContract  reproduces  Basic.lean::Contract: 302/487 = 62%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_counterInc_length  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_counterInc_potential: 106/171 = 62%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_lenSuffix_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_anyTrue_run: 512/828 = 62%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_pairExtractTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_rawStripTM: 285/461 = 62%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopCall_frame  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopCall_reframe: 500/809 = 62%
   Simulation.lean::bufferedSecondCfg_step  reproduces  Simulation.lean::bufferedFirstCfg_init: 199/322 = 62%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopReplay_step  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopBorrow_step: 258/421 = 61%
   Simulation.lean::bufferedSecondCfg  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_mapVirtual: 123/201 = 61%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamReleaseTM_step_inr  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_left: 132/216 = 61%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_right  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_left: 132/216 = 61%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitPrepare_scan  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitRestore_scan: 526/861 = 61%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitRestore_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_rawStrip_rewind: 442/725 = 61%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::clearTM_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::incrementTM_run_overflow: 299/491 = 61%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::seekEndTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::skipBackTM: 123/202 = 61%
   Basic.lean::traj_iff  reproduces  Basic.lean::Cfg.SameOutside.keep_blank: 80/132 = 61%
   Basic.lean::Frames.trans  reproduces  Basic.lean::Cfg.SameOutside.keep_blank: 80/132 = 61%
   Simulation.lean::bufferedSecondCfg  reproduces  Simulation.lean::bufferedScanCfg: 83/137 = 61%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopFuel_init  reproduces  Simulation.lean::bufferedFirstCfg_init: 195/322 = 61%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitPrepare_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_extract_rewind: 464/767 = 60%
   RecordTable.lean::rt_tailState_fintype  reproduces  RecordTable.lean::rt_tailState_decidableEq: 64/106 = 60%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitEmitCfg  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitPrepareScan: 62/103 = 60%
   RecordTable.lean::rt_find_skip_phase  reproduces  RecordTable.lean::rt_find_scan_phase: 344/572 = 60%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_counter_emit_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_counter_emit: 378/630 = 60%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_extract_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitPrepare_rewind: 464/776 = 60%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::skipBackTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::seekEndTM: 123/206 = 60%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_pairDupTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_incFixedTM: 283/474 = 60%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_loop_prepare  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_input_rewind: 146/245 = 60%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_lenParse_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_extract_run: 1137/1908 = 60%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitBody_restore  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitBody_rewind: 333/559 = 60%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_scanCopy_suffix  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_scanCopy_finish: 160/269 = 59%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::transferTM_spaceUsedByTape  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::clearTM_spaceUsedByTape: 258/434 = 59%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::copyTM_spaceUsedByTape  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::clearTM_spaceUsedByTape: 258/434 = 59%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_extract_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopBorrow_rewind: 454/764 = 59%
   RecordTable.lean::rt_position_run  reproduces  RecordTable.lean::rt_moveWord_run: 954/1606 = 59%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_mapVirtual_step  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_map_move: 215/362 = 59%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_rawStrip_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopBorrow_rewind: 453/764 = 59%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_rawStrip_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitPrepare_rewind: 460/776 = 59%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopBorrow_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_extract_rewind: 454/767 = 59%
   RecordTable.lean::rt_initRestTM  reproduces  RecordTable.lean::rt_tailTM: 113/191 = 59%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitEmit_double  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitPrepare_scan: 394/666 = 59%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_borrow_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_fuel_rewind: 772/1306 = 59%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_catalogFirstEntry  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitCount_firstHalt: 198/337 = 59%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_borrow_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_payload_rewind: 772/1314 = 59%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopBorrow_correct  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_borrow: 261/445 = 59%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitRestore_scan  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitCount_over: 82/140 = 59%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitPrepareScan  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitEmitCfg: 62/106 = 58%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitPrepareReady  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitEmitCfg: 62/106 = 58%
   RecordTable.lean::rt_copyState  reproduces  RecordTable.lean::rt_copyState_fintype: 76/130 = 58%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopBody_capture  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_call_run: 184/315 = 58%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_pairValid_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_anyTrue_run: 483/828 = 58%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamReleaseTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM: 148/254 = 58%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopBorrow_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_rawStrip_replay: 240/412 = 58%
   ZoneTape.lean::zonedTape_right  reproduces  ZoneTape.lean::zonedTape_right_sep: 92/158 = 58%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitRestore_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_extract_rewind: 446/767 = 58%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_payload_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_borrow_rewind: 772/1329 = 58%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_fuel_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_borrow_rewind: 772/1329 = 58%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::clearTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::incrementTM: 305/526 = 58%
   TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean::ReturnContract.release  reproduces  TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean::RoundContract.release: 774/1336 = 58%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_pairLenCheck_spaceUsed  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_stripLast_spaceUsed: 298/515 = 58%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_catalogPoly_unary_computes  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitPoly_loop_end: 423/739 = 57%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_payload_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_fuel_copy: 874/1527 = 57%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitEmit_double  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitEmit_separator: 460/804 = 57%
   Basic.lean::time_envelope  reproduces  Basic.lean::time_box: 123/215 = 57%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::Cfg.ofWords_copy_endpoint  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::clearTM_run: 220/385 = 57%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_fuel_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_fuel_copy: 872/1527 = 57%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loop_input_run_le  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loop_output_length_le: 145/254 = 57%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::copyTM_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::transferTM_run: 388/680 = 57%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::copyTM_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::incrementTM_run_overflow: 280/491 = 57%
   ZoneTape.lean::zonedTape_left  reproduces  ZoneTape.lean::zonedTape_left_sep: 92/162 = 57%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_map_suffix  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_map_block: 540/956 = 56%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_prepend_spaceUsed  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_pairValid_spaceUsed  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_id_spaceUsed  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_const_spaceUsed  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::Cfg.ofWords_copy_endpoint  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::copyTM_run: 228/404 = 56%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loop_rewind_bounded  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_catalogRewind: 245/435 = 56%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loop_rewind_bounded  reproduces  Simulation.lean::timed_rewind: 245/435 = 56%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitEmit_double  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_rawStrip_replay: 232/412 = 56%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_counter_emit  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_counter_emit_run: 378/672 = 56%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::compareTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::clearTM: 230/409 = 56%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::incrementTM_spaceUsedByTape  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::clearTM_spaceUsedByTape: 244/434 = 56%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_mapSetup_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 128/228 = 56%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitRestore_first  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitPrepare_first: 151/269 = 56%
   RecordTable.lean::joinFields_cfgRecord_length  reproduces  RecordTable.lean::cfgRecord_init: 111/198 = 56%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitEmbed_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_left: 121/216 = 56%
   RecordTable.lean::rt_richWindow_run  reproduces  RecordTable.lean::rt_moveWord_run: 897/1606 = 56%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_heads_join  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_heads_halted: 72/129 = 56%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::transferTM_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::incrementTM_run_overflow: 274/491 = 56%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::Cfg.ofWords_transfer_endpoint  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::copyTM_run: 225/404 = 56%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_prepend_spaceUsed  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_pairValid_spaceUsed  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_id_spaceUsed  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_const_spaceUsed  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_extract_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_pairValid_run: 679/1231 = 55%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::catalog_increment_trace  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::step_of_tapeAction_write: 92/167 = 55%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::catalog_increment_trace  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::step_of_tapeAction_move: 92/167 = 55%
   RecordTable.lean::rt_copyState  reproduces  RecordTable.lean::rt_copyState_decidableEq: 76/138 = 55%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_scanCopy_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_scanCopy_finish: 148/269 = 55%
   Simulation.lean::rewind_from_any  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_catalogRewind: 239/435 = 55%
   Simulation.lean::rewind_from_any  reproduces  Simulation.lean::timed_rewind: 239/435 = 55%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_call_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_halt_return: 279/508 = 55%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_extract_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitRestore_rewind: 446/814 = 55%
   ZoneTape.lean::zonedTape_left_word  reproduces  ZoneTape.lean::zonedTape_right_word: 285/522 = 55%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitBody_prepare  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitBody_restore: 285/523 = 54%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_extract_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_map_parse: 1035/1903 = 54%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_rawStrip_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitRestore_rewind: 442/814 = 54%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_lenParse_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_pairValid_run: 668/1231 = 54%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_pairMapSnd_spaceUsed  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_heads_halted: 70/129 = 54%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_map_parse  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_extract_run: 1035/1908 = 54%
   Simulation.lean::bufferTape_append  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_catalogBuffer_erase: 64/118 = 54%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitEmit_double  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_pairDup_double: 656/1212 = 54%
   Zone.lean::zoneCascadeRight_lengths  reproduces  Zone.lean::zoneStepPair_below: 314/582 = 54%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitCount_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 123/228 = 54%
   TCSlib/Complexity/TuringMachine/Build/Contract/Catalog.lean::transferMapTM_contract  reproduces  TCSlib/Complexity/TuringMachine/Build/Contract/Catalog.lean::copyTM_contract: 76/141 = 54%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_fuel_copy  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_fuel_return: 736/1366 = 54%
   Zone.lean::zoneShiftIndex_extend  reproduces  Zone.lean::zoneShiftIndex_extend_of_lt: 179/334 = 54%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_runFrom_left  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_mapSetup_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Simulation.lean::bufferedFirstCfg_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_runFrom_left  reproduces  Simulation.lean::bufferedFirstCfg_run: 122/228 = 54%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopCall_heads  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_fuel_heads: 329/615 = 53%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_space_of_time  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_heads_halted: 69/129 = 53%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_segments  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_heads_halted: 69/129 = 53%
   Simulation.lean::ComputesInTime.spaceUsed_le  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_heads_halted: 69/129 = 53%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitPrepare_extra  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitPrepare_scan: 356/666 = 53%
   TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean::Traj.seq  reproduces  TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean::Frames.seq: 163/305 = 53%
   Basic.lean::Contract  reproduces  Basic.lean::RoundContract: 302/566 = 53%
   Simulation.lean::bufferedScanCfg_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitPrepare_rewind: 414/776 = 53%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitEmit_suffix  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopReplay_run: 187/351 = 53%
   TCSlib/Complexity/TuringMachine/Build/Contract/Catalog.lean::seekStartTM_contract  reproduces  TCSlib/Complexity/TuringMachine/Build/Contract/Catalog.lean::seekEndTM_contract: 207/390 = 53%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_mapVirtual  reproduces  Simulation.lean::bufferedSecondCfg: 123/232 = 53%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_pairValid_computes  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_anyTrue_computes: 140/265 = 53%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitCount_firstHalt  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_catalogFirstEntry: 198/375 = 53%
   ZoneTape.lean::zoneOwner_beyond  reproduces  ZoneTape.lean::zoneOwner_sep: 105/199 = 53%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_map_block  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_extract_block: 355/675 = 53%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_pairDup_computes  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_scanStep_right: 86/164 = 52%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitCount_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_catalogPoly_setup  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_catalogPoly_emit  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_mapSetup_stationary  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_mapSetup_heads  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_timed_control_init  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_control_heads: 88/169 = 52%
   RecordTable.lean::rt_tail_run  reproduces  RecordTable.lean::rt_moveWord_run: 836/1606 = 52%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopReady_call  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopCall_reframe: 421/809 = 52%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_rawStrip_copy  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_rawStrip_replay: 214/412 = 52%
   Simulation.lean::bufferedScanCfg  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_mapCfg: 69/133 = 52%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_poly_step  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_mapSetup_step: 113/218 = 52%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopBorrow_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_extract_replay_finish: 159/307 = 52%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_map_move  reproduces  Simulation.lean::leftCfg_apply: 97/188 = 52%
   TCSlib/Complexity/TuringMachine/Build/Contract/Catalog.lean::copyMapTM_contract  reproduces  TCSlib/Complexity/TuringMachine/Build/Contract/Catalog.lean::transferMapTM_contract: 120/233 = 52%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::Cfg.ofWords_transfer_endpoint  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::clearTM_run: 198/385 = 51%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopFuelCaptured_frame  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopControl_payload: 128/249 = 51%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_catalogRewind  reproduces  Simulation.lean::rewind_from_any: 239/466 = 51%
   Simulation.lean::timed_rewind  reproduces  Simulation.lean::rewind_from_any: 239/466 = 51%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::exists_loopTM_spaceUsed  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_exists_loopFind_space: 939/1831 = 51%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_mapVirtual_step  reproduces  Simulation.lean::bufferedSecondCfg_step: 742/1449 = 51%
   Simulation.lean::bufferedSecondCfg_step  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_mapVirtual_step: 742/1452 = 51%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_release  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopCall_frame: 269/527 = 51%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitRestore_scan  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitPrepare_extra: 240/472 = 51%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitPrepare_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopBorrow_rewind: 388/764 = 51%
   TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean::branch  reproduces  TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean::seq: 1194/2353 = 51%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_counter_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::catalog_redirect_loop: 71/140 = 51%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_map_setup  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopFuel_init: 214/422 = 51%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_map_move  reproduces  Simulation.lean::rightCfg_apply: 97/192 = 51%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::skipTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::skipBackTM: 102/202 = 50%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_map_reject  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_map_launch: 374/741 = 50%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_mapCfg  reproduces  Simulation.lean::bufferedScanCfg: 69/137 = 50%
   ZoneTape.lean::zonedTape_right_sep  reproduces  ZoneTape.lean::zonedTape_right: 92/183 = 50%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::compareTM_run_stop_ofCfg  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::compareTM_run: 193/384 = 50%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_frame_replay  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopControl_payload: 125/249 = 50%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_id_spaceUsed  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_idTM_run: 388/773 = 50%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_polyUnary_spaceUsed  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_unary_sharp: 176/351 = 50%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_loop_round  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_round: 1059/2114 = 50%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::transferTM_spaceUsedByTape  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::compareTM_spaceUsedByTape: 319/637 = 50%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::copyTM_spaceUsedByTape  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::compareTM_spaceUsedByTape: 319/637 = 50%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopBorrow_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitPrepare_rewind: 388/776 = 50%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_fuel_heads  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopCall_heads: 329/658 = 50%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_pairExtractTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopDebitTM: 219/438 = 50%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_extract_replay_finish  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_rawStrip_replay: 206/412 = 50%
   ZoneTape.lean::zonedTape_left  reproduces  ZoneTape.lean::zonedTape_right_sep: 79/158 = 50%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::catalog_transferMap_trace  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::catalog_write_take: 62/124 = 50%
```

### Screen after (complete)

```text
declarations screened: 808; copy pairs (target reproduces >= half of source): 439; reproduced text: 127,994 chars
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_space_of_time  reproduces  Simulation.lean::ComputesInTime.spaceUsed_le: 713/713 = 100%
   Simulation.lean::ComputesInTime.spaceUsed_le  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_space_of_time: 713/713 = 100%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_catalogRewind  reproduces  Simulation.lean::timed_rewind: 435/435 = 100%
   Simulation.lean::timed_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_catalogRewind: 435/435 = 100%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_finSumEquiv  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_mapSumEquiv: 362/362 = 100%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_mapSumEquiv  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_finSumEquiv: 362/362 = 100%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::step_of_tapeAction_write  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::step_of_tapeAction_move: 167/167 = 100%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::step_of_tapeAction_move  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::step_of_tapeAction_write: 167/167 = 100%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamReleaseTM_step_inr  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_right: 135/135 = 100%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_right  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamReleaseTM_step_inr: 135/135 = 100%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::seekEndTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::skipTM: 129/129 = 100%
   TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean::branch_positive  reproduces  TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean::seq_positive: 62/62 = 100%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_payload_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_fuel_rewind: 1304/1306 = 100%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loop_rewind_bounded  reproduces  Simulation.lean::rewind_from_any: 465/466 = 100%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::transferTM_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::Cfg.ofWords_transfer_endpoint: 478/480 = 100%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_fuel_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_payload_rewind: 1304/1314 = 99%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::copyTM_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::Cfg.ofWords_copy_endpoint: 228/230 = 99%
   Zone.lean::zoneTrackTape_rebalance_right  reproduces  Zone.lean::zoneSide_rebalance_right: 266/269 = 99%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::Cfg.ofWords_transfer_endpoint  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::Cfg.ofWords_copy_endpoint: 227/230 = 99%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::transferTM_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::Cfg.ofWords_copy_endpoint: 225/230 = 98%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_left  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamReleaseTM_step_inr: 132/135 = 98%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_left  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_right: 132/135 = 98%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_lenSuffix_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_lenParse_first: 312/320 = 98%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_pairSnd_spaceUsed  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_pairConcat_spaceUsed: 305/314 = 97%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_pairFst_spaceUsed  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_pairConcat_spaceUsed: 305/314 = 97%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_scanTrues_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_scanStep_right: 159/164 = 97%
   Zone.lean::zoneShiftOut  reproduces  Zone.lean::zoneShiftIn: 314/324 = 97%
   Zone.lean::zoneSide_rebalance_right  reproduces  Zone.lean::zoneTrackTape_rebalance_right: 266/275 = 97%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_pairConcat_spaceUsed  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_pairSnd_spaceUsed: 305/317 = 96%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_pairConcat_spaceUsed  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_pairFst_spaceUsed: 305/317 = 96%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::transferTM_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::copyTM_run: 388/404 = 96%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::transferMapTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::copyMapTM: 478/498 = 96%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::clearTM_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::Cfg.ofWords_copy_endpoint: 220/230 = 96%
   Zone.lean::zoneShiftIn  reproduces  Zone.lean::zoneShiftOut: 314/329 = 95%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_extract_replay  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_rawStrip_replay: 393/412 = 95%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_anchor_return  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_call_run: 299/315 = 95%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopCall_reframe  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopCall_frame: 500/527 = 95%
   ZoneTape.lean::zoneOwner_sep  reproduces  ZoneTape.lean::zoneOwner_beyond: 105/111 = 95%
   Basic.lean::RoundContract  reproduces  Basic.lean::ReturnContract: 412/436 = 94%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_incFixed_computes  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_scanStep_right: 154/164 = 94%
   ZoneTape.lean::zonedTape_left  reproduces  ZoneTape.lean::zonedTape_right: 171/183 = 93%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_pairDup_double  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_scanStep_right: 152/164 = 93%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_pairSnd_spaceUsed  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_pairFst_spaceUsed: 293/317 = 92%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_pairFst_spaceUsed  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_pairSnd_spaceUsed: 293/317 = 92%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_branch_space  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::catalog_space_one: 115/125 = 92%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_map_block  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_map_move: 331/362 = 91%
   Simulation.lean::rewind_heads  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_catalogRewind: 395/435 = 91%
   Simulation.lean::rewind_heads  reproduces  Simulation.lean::timed_rewind: 395/435 = 91%
   Simulation.lean::rewind_from_any  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loop_rewind_bounded: 465/514 = 90%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitEmbed_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamReleaseTM_step_inr: 122/135 = 90%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitEmbed_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_right: 122/135 = 90%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::copyMapTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::clearTM: 369/409 = 90%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_map_suffix  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_map_move: 326/362 = 90%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::incrementTM_run_succ_ofCfg  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::incrementTM_run_overflow_ofCfg: 617/686 = 90%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::copyMapTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::transferMapTM: 478/533 = 90%
   ZoneTape.lean::zonedTape_right  reproduces  ZoneTape.lean::zonedTape_left: 171/191 = 90%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_halt_return  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_call_run: 279/315 = 89%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::copyTM_spaceUsedByTape  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::transferTM_spaceUsedByTape: 625/713 = 88%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::copyTM_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::clearTM_run: 336/385 = 87%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_extract_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_rawStrip_rewind: 632/725 = 87%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_borrow_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopBorrow_run: 414/476 = 87%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_map_backB  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_map_backA: 806/927 = 87%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_body_capture  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_fuel_capture: 96/111 = 86%
   TCSlib/Complexity/TuringMachine/Build/Contract/Catalog.lean::transferMapTM_contract  reproduces  TCSlib/Complexity/TuringMachine/Build/Contract/Catalog.lean::copyMapTM_contract: 120/139 = 86%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::transferTM_spaceUsedByTape  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::copyTM_spaceUsedByTape: 625/727 = 86%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitRestore_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitPrepare_rewind: 664/776 = 86%
   Basic.lean::Cfg.SameOutside.keep_blank  reproduces  Basic.lean::endpoint_not_mem: 97/114 = 85%
   TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean::seq_positive  reproduces  TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean::branch_positive: 62/73 = 85%
   Basic.lean::safeSegment_iff  reproduces  Basic.lean::segment_iff: 84/99 = 85%
   Basic.lean::time_box  reproduces  Basic.lean::time_envelope: 123/146 = 84%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::transferMapTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::clearTM: 344/409 = 84%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::seekStartTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::seekEndTM: 173/206 = 84%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_call_heads  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_fuel_heads: 515/615 = 84%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_fuel_return  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_fuel_rewind: 1092/1306 = 84%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::clearTM_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::copyTM_run: 336/404 = 83%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_fuel_return  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_payload_rewind: 1092/1314 = 83%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_map_backA  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_map_backB: 806/975 = 83%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_rawStrip_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_extract_rewind: 632/767 = 82%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_fuel_capture  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_body_capture: 96/117 = 82%
   Basic.lean::hullLo  reproduces  Basic.lean::hullHi: 114/139 = 82%
   Basic.lean::hullHi  reproduces  Basic.lean::hullLo: 114/139 = 82%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitPrepare_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitRestore_rewind: 664/814 = 82%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::transferTM_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::clearTM_run: 314/385 = 82%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_sum_add  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_map_sum: 153/188 = 81%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_map_sum  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_sum_add: 153/188 = 81%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_fuel_return  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_borrow_rewind: 1077/1329 = 81%
   Simulation.lean::rightCfg_step  reproduces  Simulation.lean::leftCfg_step: 306/378 = 81%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::step_of_tapeAction_write  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::step_of_inputMoveAction: 68/84 = 81%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::step_of_tapeAction_move  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::step_of_inputMoveAction: 68/84 = 81%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_counter_count_space  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_counter_count: 363/452 = 80%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::seekStartTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::skipBackTM: 162/202 = 80%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_payload_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_fuel_return: 1092/1366 = 80%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_fuel_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_fuel_return: 1092/1366 = 80%
   Simulation.lean::leftCfg_step  reproduces  Simulation.lean::rightCfg_step: 306/384 = 80%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_extract_suffix  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_extract_first: 238/300 = 79%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::skipBackTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::skipTM: 102/129 = 79%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_call_heads  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopCall_heads: 520/658 = 79%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitRestore_scan  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitPrepare_scan: 526/666 = 79%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_borrow_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_fuel_return: 1077/1366 = 79%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_branch_space  reproduces  Simulation.lean::branchTM_computes: 632/802 = 79%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::transferTM_run_ofCfg  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::copyTM_run_ofCfg: 89/113 = 79%
   Simulation.lean::bufferedFirstCfg_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_mapSetup_run: 128/163 = 79%
   ZoneTape.lean::zonedTape_left_sep  reproduces  ZoneTape.lean::zonedTape_right_sep: 124/158 = 78%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::seekStartTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::skipTM: 101/129 = 78%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::incrementTM_run_succ  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::incrementTM_run_overflow: 383/491 = 78%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_loop_prepare  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_prepare: 1165/1499 = 78%
   Basic.lean::endpoint_not_mem  reproduces  Basic.lean::traj_iff: 80/103 = 78%
   Basic.lean::Frames.trans  reproduces  Basic.lean::traj_iff: 80/103 = 78%
   Basic.lean::Cfg.SameOutside.keep_blank  reproduces  Basic.lean::traj_iff: 80/103 = 78%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::incrementTM_run_overflow  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::clearTM_run: 299/385 = 78%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::compareTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::incrementTM: 408/526 = 78%
   ZoneTape.lean::zonedTape_right_sep  reproduces  ZoneTape.lean::zonedTape_left_sep: 124/162 = 77%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_counterTape_write  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopBuffer_write: 311/408 = 76%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_scanCopy_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_scanStep_right: 125/164 = 76%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopBorrow_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_borrow_run: 414/544 = 76%
   Basic.lean::round_iff  reproduces  Basic.lean::segment_iff: 75/99 = 76%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopBorrow_step  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopReplay_step: 258/341 = 76%
   Simulation.lean::rightCfg_apply  reproduces  Simulation.lean::leftCfg_apply: 142/188 = 76%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamReleaseTM: 148/196 = 76%
   Zone.lean::zoneMoveRight  reproduces  Zone.lean::zoneMoveLeft: 336/445 = 76%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitCount_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_mapSetup_run: 123/163 = 75%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitPrepare_scan  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitPrepare_extra: 356/472 = 75%
   Zone.lean::zoneSide_shiftOutW  reproduces  Zone.lean::zoneSide_shiftInW: 296/394 = 75%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_extract_replay  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_extract_replay_finish: 230/307 = 75%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_runFrom_left  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_mapSetup_run: 122/163 = 75%
   Zone.lean::zoneMoveLeft  reproduces  Zone.lean::zoneMoveRight: 336/449 = 75%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::incrementTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::clearTM: 305/409 = 75%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_runFrom_left  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::catalog_redirect_loop  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_mapSetup_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Simulation.lean::bufferedFirstCfg_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::compareTM_spaceUsedByTape  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::compareTM_run: 286/384 = 74%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_counterInc_potential  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_counterInc_length: 106/143 = 74%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::clearTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::copyMapTM: 369/498 = 74%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_extract_block  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_extract_first: 222/300 = 74%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopCall_heads  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_call_heads: 520/703 = 74%
   Simulation.lean::leftCfg_apply  reproduces  Simulation.lean::rightCfg_apply: 142/192 = 74%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::incrementTM_run_overflow_ofCfg  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::incrementTM_run_succ_ofCfg: 617/839 = 74%
   Basic.lean::segment_iff  reproduces  Basic.lean::round_iff: 75/102 = 74%
   Basic.lean::safeSegment_iff  reproduces  Basic.lean::round_iff: 75/102 = 74%
   Basic.lean::endpoint_not_mem  reproduces  Basic.lean::Cfg.SameOutside.keep_blank: 97/132 = 73%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::incrementTM_run_succ  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::Cfg.ofWords_copy_endpoint: 169/230 = 73%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::incrementTM_run_overflow  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::Cfg.ofWords_copy_endpoint: 169/230 = 73%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loop_find_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_loop_halted_run: 484/659 = 73%
   Simulation.lean::bufferedSecondCfg_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_mapVirtual_run: 190/259 = 73%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopFrame  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopControlAction: 110/150 = 73%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_incFixedTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_pairDupTM: 283/386 = 73%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_fuel_heads  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_call_heads: 515/703 = 73%
   RecordTable.lean::rt_copyState_fintype  reproduces  RecordTable.lean::rt_copyState: 76/104 = 73%
   RecordTable.lean::rt_copyState_decidableEq  reproduces  RecordTable.lean::rt_copyState: 76/104 = 73%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_counterTape_read  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopBuffer_read: 65/89 = 73%
   Simulation.lean::bufferedFirstCfg_step  reproduces  Simulation.lean::bufferedFirstCfg_init: 235/322 = 73%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_catalogPoly_setup  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_catalogPoly_emit: 384/527 = 73%
   Basic.lean::ReturnContract  reproduces  Basic.lean::RoundContract: 412/566 = 73%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_mapSetup_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_runFrom_left: 122/168 = 73%
   Simulation.lean::bufferedFirstCfg_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_runFrom_left: 122/168 = 73%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_anchor_return  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopBody_capture: 270/372 = 73%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitCount_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_mapSetup_heads: 71/98 = 72%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_mapSetup_stationary  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_mapSetup_heads: 71/98 = 72%
   ZoneRebalance.lean::zr_pair_pass  reproduces  ZoneRebalance.lean::zr_inPass_out: 92/127 = 72%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_spaceUsedByTape_le_max  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_spaceUsedByTape_le_add: 92/127 = 72%
   Zone.lean::zoneShiftIndex_nonempty  reproduces  Zone.lean::zoneShiftIndex_le: 80/111 = 72%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopBuffer_write  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_counterTape_write: 311/432 = 72%
   Simulation.lean::rightAction  reproduces  Simulation.lean::leftAction: 69/96 = 72%
   Simulation.lean::leftAction  reproduces  Simulation.lean::rightAction: 69/96 = 72%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitRestoreScan  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitPrepareScan: 74/103 = 72%
   Basic.lean::locate  reproduces  Basic.lean::cut: 219/305 = 72%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitRestore_append  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitPrepare_extra: 338/472 = 72%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitCount_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_runFrom_left: 120/168 = 71%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_loop_halted_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loop_find_run: 484/678 = 71%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_borrow  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopBorrow_correct: 261/367 = 71%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_map_setup  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_map_move: 257/362 = 71%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_rawStripTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopReplayTM: 92/130 = 71%
   RecordTable.lean::rt_copyState_decidableEq  reproduces  RecordTable.lean::rt_copyState_fintype: 92/130 = 71%
   Simulation.lean::branchTM_computes  reproduces  Simulation.lean::leftCfg_apply: 133/188 = 71%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_firstReturn  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_run: 151/214 = 71%
   Simulation.lean::branchTM_computes  reproduces  Simulation.lean::rightCfg_apply: 135/192 = 70%
   Simulation.lean::rightCfg_run  reproduces  Simulation.lean::leftCfg_run: 71/101 = 70%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::Cfg.ofWords_transfer_endpoint  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::transferTM_run: 478/680 = 70%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_cond_ledger  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_timed_start: 754/1073 = 70%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitRestoreTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitPrepareTM: 280/399 = 70%
   Basic.lean::traj_iff  reproduces  Basic.lean::endpoint_not_mem: 80/114 = 70%
   Basic.lean::Frames.trans  reproduces  Basic.lean::endpoint_not_mem: 80/114 = 70%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::incrementTM_run_succ  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::clearTM_run: 270/385 = 70%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_extract_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_extract_replay_finish: 215/307 = 70%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_heads_halted  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_heads_join: 72/103 = 70%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopBody_step  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopBody_stop: 245/352 = 70%
   Simulation.lean::bufferedScanCfg_run  reproduces  Simulation.lean::bufferedFirstCfg_init: 224/322 = 70%
   Simulation.lean::bufferedFirstCfg_rewind  reproduces  Simulation.lean::bufferedFirstCfg_init: 224/322 = 70%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_lenParse_block  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_lenParse_first: 222/320 = 69%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::incrementTM_run_overflow  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::copyTM_run: 280/404 = 69%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::catalogIncR  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::catalogCompareR: 63/91 = 69%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_mapVirtual  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_mapCfg: 92/133 = 69%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::catalogIncF  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::catalogIncR: 152/220 = 69%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::copyTM_run_ofCfg  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::transferTM_run_ofCfg: 89/129 = 69%
   Simulation.lean::leftCfg_run  reproduces  Simulation.lean::rightCfg_run: 71/103 = 69%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::seekEndTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::seekStartTM: 173/251 = 69%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitEmbed_cut  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamReleaseTM_step_inr: 93/135 = 69%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitEmbed_cut  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_right: 93/135 = 69%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_incFixed_spaceUsed  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_pairDup_spaceUsed: 74/108 = 69%
   TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean::RoundContract.release  reproduces  TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean::ReturnContract.release: 774/1135 = 68%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_counter_heads  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_counter_computes: 666/977 = 68%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_counterInc_bits  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopValue_bits: 96/141 = 68%
   RecordTable.lean::rt_find_scan_phase  reproduces  RecordTable.lean::rt_find_skip_phase: 344/508 = 68%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_anchor_return  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_halt_return: 342/508 = 67%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_pairDup_spaceUsed  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_incFixed_spaceUsed: 74/110 = 67%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::catalog_transferMap_trace  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::catalog_clear_trace: 1086/1617 = 67%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_rawStrip_replay  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_extract_replay_finish: 206/307 = 67%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_rawStrip_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_rawStrip_replay: 276/412 = 67%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_rawStrip_replay  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_extract_replay: 393/587 = 67%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_mapVirtual_run  reproduces  Simulation.lean::bufferedSecondCfg_run: 190/284 = 67%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_fuel_copy  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_fuel_rewind: 872/1306 = 67%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_extract_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_lenParse_run: 1137/1703 = 67%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::catalogIncR  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::catalogIncF: 152/228 = 67%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::scanResult_fold  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::scanResult_map: 92/138 = 67%
   RecordTable.lean::rt_copyState_fintype  reproduces  RecordTable.lean::rt_copyState_decidableEq: 92/138 = 67%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::incrementTM_run_succ  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::copyTM_run: 269/404 = 67%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_fuel_copy  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_payload_rewind: 874/1314 = 67%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_catalogRewind  reproduces  Simulation.lean::rewind_heads: 395/594 = 66%
   Simulation.lean::timed_rewind  reproduces  Simulation.lean::rewind_heads: 395/594 = 66%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_scanCopy_suffix  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_scanStep_right: 109/164 = 66%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_map_suffix  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_map_first: 232/351 = 66%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitPrepareScan  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitRestoreScan: 74/112 = 66%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_branch_space  reproduces  Simulation.lean::leftCfg_apply: 124/188 = 66%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_incFixedTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitRewindTM: 122/185 = 66%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_branch_space  reproduces  Simulation.lean::rightCfg_apply: 126/192 = 66%
   RecordTable.lean::rt_tailState_decidableEq  reproduces  RecordTable.lean::rt_tailState_fintype: 64/98 = 65%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopReady_call  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopCall_frame: 344/527 = 65%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_poly_space  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_space_radius: 239/367 = 65%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamReleaseTM_step_inr  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitEmbed_run: 122/188 = 65%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_right  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitEmbed_run: 122/188 = 65%
   Simulation.lean::rightCfg  reproduces  Simulation.lean::leftCfg: 84/130 = 65%
   Simulation.lean::leftCfg  reproduces  Simulation.lean::rightCfg: 84/130 = 65%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::skipBackTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::seekStartTM: 162/251 = 65%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::clearTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::transferMapTM: 344/533 = 65%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_timed_read  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_control_heads: 109/169 = 64%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_left  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitEmbed_run: 121/188 = 64%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitEmbed_cut  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitEmbed_run: 121/188 = 64%
   Simulation.lean::bufferedScanCfg_run  reproduces  Simulation.lean::bufferedFirstCfg_rewind: 473/735 = 64%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_catalogPoly_emit  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_catalogPoly_setup: 384/598 = 64%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_counter_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_counter_emit_run: 431/672 = 64%
   Zone.lean::zoneSide_shiftInW  reproduces  Zone.lean::zoneSide_shiftOutW: 296/462 = 64%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_firstReturn: 151/237 = 64%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_extract_suffix  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_scanCopy_suffix: 553/868 = 64%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitBody_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitBody_restore: 333/523 = 64%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitPrepare_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_rawStrip_rewind: 460/725 = 63%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::scanResult_map  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::scanResult_fold: 92/145 = 63%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_pairExtractTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopReplayTM: 82/130 = 63%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_read_heads  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_control_heads: 106/169 = 63%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_pairDupTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitRewindTM: 116/185 = 63%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::incrementTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::compareTM: 408/651 = 63%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::skipTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::seekEndTM: 129/206 = 63%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_pairDup_double  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_scanCopy_run: 311/497 = 63%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopBorrow_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_rawStrip_rewind: 453/725 = 62%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_extract_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_rawStrip_replay: 257/412 = 62%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_rawStrip_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_extract_replay_finish: 191/307 = 62%
   Zone.lean::zoneShiftIndex_nonempty  reproduces  Zone.lean::zoneShiftIndex_empty: 115/185 = 62%
   Basic.lean::RoundContract  reproduces  Basic.lean::Contract: 302/487 = 62%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_counterInc_length  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_counterInc_potential: 106/171 = 62%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_lenSuffix_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_anyTrue_run: 512/828 = 62%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_pairExtractTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_rawStripTM: 285/461 = 62%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopCall_frame  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopCall_reframe: 500/809 = 62%
   Simulation.lean::bufferedSecondCfg_step  reproduces  Simulation.lean::bufferedFirstCfg_init: 199/322 = 62%
   ZoneRebalance.lean::zr_inPass_out  reproduces  ZoneRebalance.lean::zr_pair_pass: 92/149 = 62%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopReplay_step  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopBorrow_step: 258/421 = 61%
   Simulation.lean::bufferedSecondCfg  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_mapVirtual: 123/201 = 61%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamReleaseTM_step_inr  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_left: 132/216 = 61%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_right  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_left: 132/216 = 61%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitPrepare_scan  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitRestore_scan: 526/861 = 61%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitRestore_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_rawStrip_rewind: 442/725 = 61%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::clearTM_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::incrementTM_run_overflow: 299/491 = 61%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::seekEndTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::skipBackTM: 123/202 = 61%
   Basic.lean::traj_iff  reproduces  Basic.lean::Cfg.SameOutside.keep_blank: 80/132 = 61%
   Basic.lean::Frames.trans  reproduces  Basic.lean::Cfg.SameOutside.keep_blank: 80/132 = 61%
   Simulation.lean::bufferedSecondCfg  reproduces  Simulation.lean::bufferedScanCfg: 83/137 = 61%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopFuel_init  reproduces  Simulation.lean::bufferedFirstCfg_init: 195/322 = 61%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitPrepare_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_extract_rewind: 464/767 = 60%
   RecordTable.lean::rt_tailState_fintype  reproduces  RecordTable.lean::rt_tailState_decidableEq: 64/106 = 60%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitEmitCfg  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitPrepareScan: 62/103 = 60%
   RecordTable.lean::rt_find_skip_phase  reproduces  RecordTable.lean::rt_find_scan_phase: 344/572 = 60%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_counter_emit_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_counter_emit: 378/630 = 60%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_extract_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitPrepare_rewind: 464/776 = 60%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::skipBackTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::seekEndTM: 123/206 = 60%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_pairDupTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_incFixedTM: 283/474 = 60%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_loop_prepare  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_input_rewind: 146/245 = 60%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_lenParse_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_extract_run: 1137/1908 = 60%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitBody_restore  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitBody_rewind: 333/559 = 60%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_scanCopy_suffix  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_scanCopy_finish: 160/269 = 59%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::transferTM_spaceUsedByTape  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::clearTM_spaceUsedByTape: 258/434 = 59%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::copyTM_spaceUsedByTape  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::clearTM_spaceUsedByTape: 258/434 = 59%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_extract_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopBorrow_rewind: 454/764 = 59%
   RecordTable.lean::rt_position_run  reproduces  RecordTable.lean::rt_moveWord_run: 954/1606 = 59%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_mapVirtual_step  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_map_move: 215/362 = 59%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_rawStrip_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopBorrow_rewind: 453/764 = 59%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_rawStrip_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitPrepare_rewind: 460/776 = 59%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopBorrow_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_extract_rewind: 454/767 = 59%
   RecordTable.lean::rt_initRestTM  reproduces  RecordTable.lean::rt_tailTM: 113/191 = 59%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitEmit_double  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitPrepare_scan: 394/666 = 59%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_borrow_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_fuel_rewind: 772/1306 = 59%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_catalogFirstEntry  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitCount_firstHalt: 198/337 = 59%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_borrow_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_payload_rewind: 772/1314 = 59%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopBorrow_correct  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_borrow: 261/445 = 59%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitRestore_scan  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitCount_over: 82/140 = 59%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitPrepareScan  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitEmitCfg: 62/106 = 58%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitPrepareReady  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitEmitCfg: 62/106 = 58%
   RecordTable.lean::rt_copyState  reproduces  RecordTable.lean::rt_copyState_fintype: 76/130 = 58%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopBody_capture  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_call_run: 184/315 = 58%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_pairValid_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_anyTrue_run: 483/828 = 58%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamReleaseTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM: 148/254 = 58%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopBorrow_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_rawStrip_replay: 240/412 = 58%
   ZoneTape.lean::zonedTape_right  reproduces  ZoneTape.lean::zonedTape_right_sep: 92/158 = 58%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitRestore_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_extract_rewind: 446/767 = 58%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_payload_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_borrow_rewind: 772/1329 = 58%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_fuel_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_borrow_rewind: 772/1329 = 58%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::clearTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::incrementTM: 305/526 = 58%
   TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean::ReturnContract.release  reproduces  TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean::RoundContract.release: 774/1336 = 58%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_pairLenCheck_spaceUsed  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_stripLast_spaceUsed: 298/515 = 58%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_catalogPoly_unary_computes  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitPoly_loop_end: 423/739 = 57%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_payload_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_fuel_copy: 874/1527 = 57%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitEmit_double  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitEmit_separator: 460/804 = 57%
   Basic.lean::time_envelope  reproduces  Basic.lean::time_box: 123/215 = 57%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::Cfg.ofWords_copy_endpoint  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::clearTM_run: 220/385 = 57%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_fuel_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_fuel_copy: 872/1527 = 57%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loop_input_run_le  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loop_output_length_le: 145/254 = 57%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::copyTM_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::transferTM_run: 388/680 = 57%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::copyTM_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::incrementTM_run_overflow: 280/491 = 57%
   ZoneTape.lean::zonedTape_left  reproduces  ZoneTape.lean::zonedTape_left_sep: 92/162 = 57%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_map_suffix  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_map_block: 540/956 = 56%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_prepend_spaceUsed  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_pairValid_spaceUsed  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_id_spaceUsed  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_const_spaceUsed  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::Cfg.ofWords_copy_endpoint  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::copyTM_run: 228/404 = 56%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loop_rewind_bounded  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_catalogRewind: 245/435 = 56%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loop_rewind_bounded  reproduces  Simulation.lean::timed_rewind: 245/435 = 56%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitEmit_double  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_rawStrip_replay: 232/412 = 56%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_counter_emit  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_counter_emit_run: 378/672 = 56%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::compareTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::clearTM: 230/409 = 56%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::incrementTM_spaceUsedByTape  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::clearTM_spaceUsedByTape: 244/434 = 56%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_mapSetup_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 128/228 = 56%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitRestore_first  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitPrepare_first: 151/269 = 56%
   RecordTable.lean::joinFields_cfgRecord_length  reproduces  RecordTable.lean::cfgRecord_init: 111/198 = 56%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitEmbed_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_left: 121/216 = 56%
   RecordTable.lean::rt_richWindow_run  reproduces  RecordTable.lean::rt_moveWord_run: 897/1606 = 56%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_heads_join  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_heads_halted: 72/129 = 56%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::transferTM_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::incrementTM_run_overflow: 274/491 = 56%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::Cfg.ofWords_transfer_endpoint  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::copyTM_run: 225/404 = 56%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_prepend_spaceUsed  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_pairValid_spaceUsed  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_id_spaceUsed  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_const_spaceUsed  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_extract_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_pairValid_run: 679/1231 = 55%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::catalog_increment_trace  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::step_of_tapeAction_write: 92/167 = 55%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::catalog_increment_trace  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::step_of_tapeAction_move: 92/167 = 55%
   RecordTable.lean::rt_copyState  reproduces  RecordTable.lean::rt_copyState_decidableEq: 76/138 = 55%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_scanCopy_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_scanCopy_finish: 148/269 = 55%
   Simulation.lean::rewind_from_any  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_catalogRewind: 239/435 = 55%
   Simulation.lean::rewind_from_any  reproduces  Simulation.lean::timed_rewind: 239/435 = 55%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_call_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_halt_return: 279/508 = 55%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_extract_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitRestore_rewind: 446/814 = 55%
   ZoneTape.lean::zonedTape_left_word  reproduces  ZoneTape.lean::zonedTape_right_word: 285/522 = 55%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitBody_prepare  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitBody_restore: 285/523 = 54%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_extract_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_map_parse: 1035/1903 = 54%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_rawStrip_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitRestore_rewind: 442/814 = 54%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_lenParse_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_pairValid_run: 668/1231 = 54%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_pairMapSnd_spaceUsed  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_heads_halted: 70/129 = 54%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_map_parse  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_extract_run: 1035/1908 = 54%
   Simulation.lean::bufferTape_append  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_catalogBuffer_erase: 64/118 = 54%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitEmit_double  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_pairDup_double: 656/1212 = 54%
   Zone.lean::zoneCascadeRight_lengths  reproduces  Zone.lean::zoneStepPair_below: 314/582 = 54%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitCount_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 123/228 = 54%
   TCSlib/Complexity/TuringMachine/Build/Contract/Catalog.lean::transferMapTM_contract  reproduces  TCSlib/Complexity/TuringMachine/Build/Contract/Catalog.lean::copyTM_contract: 76/141 = 54%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_fuel_copy  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_fuel_return: 736/1366 = 54%
   Zone.lean::zoneShiftIndex_extend  reproduces  Zone.lean::zoneShiftIndex_extend_of_lt: 179/334 = 54%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_runFrom_left  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_mapSetup_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Simulation.lean::bufferedFirstCfg_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_runFrom_left  reproduces  Simulation.lean::bufferedFirstCfg_run: 122/228 = 54%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopCall_heads  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_fuel_heads: 329/615 = 53%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_space_of_time  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_heads_halted: 69/129 = 53%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_segments  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_heads_halted: 69/129 = 53%
   Simulation.lean::ComputesInTime.spaceUsed_le  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_heads_halted: 69/129 = 53%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitPrepare_extra  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitPrepare_scan: 356/666 = 53%
   TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean::Traj.seq  reproduces  TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean::Frames.seq: 163/305 = 53%
   Basic.lean::Contract  reproduces  Basic.lean::RoundContract: 302/566 = 53%
   Simulation.lean::bufferedScanCfg_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitPrepare_rewind: 414/776 = 53%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitEmit_suffix  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopReplay_run: 187/351 = 53%
   TCSlib/Complexity/TuringMachine/Build/Contract/Catalog.lean::seekStartTM_contract  reproduces  TCSlib/Complexity/TuringMachine/Build/Contract/Catalog.lean::seekEndTM_contract: 207/390 = 53%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_mapVirtual  reproduces  Simulation.lean::bufferedSecondCfg: 123/232 = 53%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_pairValid_computes  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_anyTrue_computes: 140/265 = 53%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitCount_firstHalt  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_catalogFirstEntry: 198/375 = 53%
   ZoneTape.lean::zoneOwner_beyond  reproduces  ZoneTape.lean::zoneOwner_sep: 105/199 = 53%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_map_block  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_extract_block: 355/675 = 53%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_pairDup_computes  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_scanStep_right: 86/164 = 52%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitCount_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_catalogPoly_setup  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_catalogPoly_emit  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_mapSetup_stationary  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_mapSetup_heads  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_timed_control_init  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_control_heads: 88/169 = 52%
   RecordTable.lean::rt_tail_run  reproduces  RecordTable.lean::rt_moveWord_run: 836/1606 = 52%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopReady_call  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopCall_reframe: 421/809 = 52%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_rawStrip_copy  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_rawStrip_replay: 214/412 = 52%
   Simulation.lean::bufferedScanCfg  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_mapCfg: 69/133 = 52%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_poly_step  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_mapSetup_step: 113/218 = 52%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopBorrow_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_extract_replay_finish: 159/307 = 52%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_map_move  reproduces  Simulation.lean::leftCfg_apply: 97/188 = 52%
   TCSlib/Complexity/TuringMachine/Build/Contract/Catalog.lean::copyMapTM_contract  reproduces  TCSlib/Complexity/TuringMachine/Build/Contract/Catalog.lean::transferMapTM_contract: 120/233 = 52%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::Cfg.ofWords_transfer_endpoint  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::clearTM_run: 198/385 = 51%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopFuelCaptured_frame  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopControl_payload: 128/249 = 51%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_catalogRewind  reproduces  Simulation.lean::rewind_from_any: 239/466 = 51%
   Simulation.lean::timed_rewind  reproduces  Simulation.lean::rewind_from_any: 239/466 = 51%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::exists_loopTM_spaceUsed  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_exists_loopFind_space: 939/1831 = 51%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_mapVirtual_step  reproduces  Simulation.lean::bufferedSecondCfg_step: 742/1449 = 51%
   Simulation.lean::bufferedSecondCfg_step  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_mapVirtual_step: 742/1452 = 51%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_release  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopCall_frame: 269/527 = 51%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitRestore_scan  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitPrepare_extra: 240/472 = 51%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitPrepare_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopBorrow_rewind: 388/764 = 51%
   TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean::branch  reproduces  TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean::seq: 1194/2353 = 51%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_counter_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::catalog_redirect_loop: 71/140 = 51%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_map_setup  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopFuel_init: 214/422 = 51%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_map_move  reproduces  Simulation.lean::rightCfg_apply: 97/192 = 51%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::skipTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::skipBackTM: 102/202 = 50%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_map_reject  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_map_launch: 374/741 = 50%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_mapCfg  reproduces  Simulation.lean::bufferedScanCfg: 69/137 = 50%
   ZoneTape.lean::zonedTape_right_sep  reproduces  ZoneTape.lean::zonedTape_right: 92/183 = 50%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::compareTM_run_stop_ofCfg  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::compareTM_run: 193/384 = 50%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_frame_replay  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopControl_payload: 125/249 = 50%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_id_spaceUsed  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_idTM_run: 388/773 = 50%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::computesFunInTime_polyUnary_spaceUsed  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_unary_sharp: 176/351 = 50%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_loop_round  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_round: 1059/2114 = 50%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::transferTM_spaceUsedByTape  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::compareTM_spaceUsedByTape: 319/637 = 50%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::copyTM_spaceUsedByTape  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::compareTM_spaceUsedByTape: 319/637 = 50%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopBorrow_rewind  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitPrepare_rewind: 388/776 = 50%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::a2_fuel_heads  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopCall_heads: 329/658 = 50%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_pairExtractTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopDebitTM: 219/438 = 50%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_extract_replay_finish  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_rawStrip_replay: 206/412 = 50%
   ZoneTape.lean::zonedTape_left  reproduces  ZoneTape.lean::zonedTape_right_sep: 79/158 = 50%
   TCSlib/Complexity/TuringMachine/Build/Catalog.lean::catalog_transferMap_trace  reproduces  TCSlib/Complexity/TuringMachine/Build/Catalog.lean::catalog_write_take: 62/124 = 50%
```

## Disk-space failure: complete failed module attempt

```text
[41/80] TCSlib/Complexity/TuringMachine/Build/Primitives
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2242:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2635:42: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2641:72: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2635:42: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2641:72: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2633:82: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2663:72: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2663:72: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2651:38: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2655:38: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2713:29: warning: This simp argument is unused:
  List.append_nil

Hint: Omit it from the simp argument list.
  simp only [↓reduceIte,̵ ̵L̵i̵s̵t̵.̵a̵p̵p̵e̵n̵d̵_̵n̵i̵l̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2676:42: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2681:42: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2684:42: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2723:46: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2747:43: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3174:25: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3174:25: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3266:59: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3414:34: warning: This simp argument is unused:
  splitRestoreScan

Hint: Omit it from the simp argument list.
  simp [Action.apply,̵ ̵s̵p̵l̵i̵t̵R̵e̵s̵t̵o̵r̵e̵S̵c̵a̵n̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3444:79: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3444:79: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3507:6: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3552:52: warning: This simp argument is unused:
  Nat.cast_one

Hint: Omit it from the simp argument list.
  simp only [List.length_nil, Nat.zero_add, N̵a̵t̵.̵c̵a̵s̵t̵_̵o̵n̵e̵,̵ ̵Fin.ext_iff, Fin.val_one] at h₁

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3552:66: warning: This simp argument is unused:
  Fin.ext_iff

Hint: Omit it from the simp argument list.
  simp only [List.length_nil, Nat.zero_add, Nat.cast_one, Fin.e̵x̵t̵_̵i̵f̵f̵,̵ ̵F̵i̵n̵.̵val_one] at h₁

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3552:79: warning: This simp argument is unused:
  Fin.val_one

Hint: Omit it from the simp argument list.
  simp only [List.length_nil, Nat.zero_add, Nat.cast_one, Fin.ext_iff,̵ ̵F̵i̵n̵.̵v̵a̵l̵_̵o̵n̵e̵] at h₁

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3592:20: warning: This simp argument is unused:
  MultiTapeTM.step

Hint: Omit it from the simp argument list.
  simp [M̵u̵l̵t̵i̵T̵a̵p̵e̵T̵M̵.̵s̵t̵e̵p̵,̵ ̵catalogPolyUnaryTM, Action.apply, catalogPolyCfg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3592:38: warning: This simp argument is unused:
  catalogPolyUnaryTM

Hint: Omit it from the simp argument list.
  simp [MultiTapeTM.step, c̵a̵t̵a̵l̵o̵g̵P̵o̵l̵y̵U̵n̵a̵r̵y̵T̵M̵,̵ ̵Action.apply, catalogPolyCfg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3592:72: warning: This simp argument is unused:
  catalogPolyCfg

Hint: Omit it from the simp argument list.
  simp [MultiTapeTM.step, catalogPolyUnaryTM, Action.apply,̵ ̵c̵a̵t̵a̵l̵o̵g̵P̵o̵l̵y̵C̵f̵g̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3593:10: warning: This simp argument is unused:
  MultiTapeTM.step

Hint: Omit it from the simp argument list.
  simp [M̵u̵l̵t̵i̵T̵a̵p̵e̵T̵M̵.̵s̵t̵e̵p̵,̵ ̵catalogPolyUnaryTM, Action.apply, catalogPolyCfg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3593:28: warning: This simp argument is unused:
  catalogPolyUnaryTM

Hint: Omit it from the simp argument list.
  simp [MultiTapeTM.step, c̵a̵t̵a̵l̵o̵g̵P̵o̵l̵y̵U̵n̵a̵r̵y̵T̵M̵,̵ ̵Action.apply, catalogPolyCfg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3593:62: warning: This simp argument is unused:
  catalogPolyCfg

Hint: Omit it from the simp argument list.
  simp [MultiTapeTM.step, catalogPolyUnaryTM, Action.apply,̵ ̵c̵a̵t̵a̵l̵o̵g̵P̵o̵l̵y̵C̵f̵g̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3640:23: warning: This simp argument is unused:
  Prod.mk.injEq

Hint: Omit it from the simp argument list.
  simp only [ht0, MultiTapeTM.runFrom_zero, splitRestoreScan, Cfg.ofWords,
      Option.some.injEq,̵ ̵P̵r̵o̵d̵.̵m̵k̵.resource exhausted (error code: 28, no space left on device)
FAIL(TCSlib/Complexity/TuringMachine/Build/Primitives): lean exited with status 1
EXIT 1
```

## Dependency-path recovery: complete failed attempt

```text
[41/80] TCSlib/Complexity/TuringMachine/Build/Primitives
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:6:0: error: object file '/workspace/scratch/9287e0d90bc1/tcslib/.lake/packages/importGraph/.lake/build/lib/lean/ImportGraph/Imports.olean' of module ImportGraph.Imports does not exist
FAIL(TCSlib/Complexity/TuringMachine/Build/Primitives): lean exited with status 1
FAIL(TCSlib/Complexity/TuringMachine/Build/Primitives): error diagnostics reported
FAIL(TCSlib/Complexity/TuringMachine/Build/Primitives): no fresh .olean produced
EXIT 1

SECOND DEPENDENCY-PATH ATTEMPT
[41/80] TCSlib/Complexity/TuringMachine/Build/Primitives
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:6:0: error: object file '/dev/shm/g4-cont1-checks/oleans/Aesop/Rule/Name.olean' of module Aesop.Rule.Name does not exist
FAIL(TCSlib/Complexity/TuringMachine/Build/Primitives): lean exited with status 1
FAIL(TCSlib/Complexity/TuringMachine/Build/Primitives): error diagnostics reported
FAIL(TCSlib/Complexity/TuringMachine/Build/Primitives): no fresh .olean produced
EXIT 1
```

## Archive contents

The archive contains this report, the full modified Lean source, one format-patch file,
the bundle, bootstrap/final/axiom logs, both screen outputs, the addendum's exact C shim
source, and `SHA256SUMS`. The checksum file covers every other archive member. There is
no compiled shim, olean, cache artifact, exploratory source, or dependency checkout.
