# Chapter 2, epoch 4, batch A3 — verified partial checkpoint

**Incomplete. No additional public target is closed.** This delivery banks
**150 new admission-free private declarations**: a native signed-position
tracker, a native recorder that actually stores every row from source time
zero through the horizon, a native signed-position comparator, and a native
sequential field reader. Their local runtime and complete-configuration
contracts are proved. The four original assigned admissions remain untouched;
there are no new admissions and no sanctioned admitted dependencies.

**The complete packed-record producer remains open.** This checkpoint is
before the brief's natural complete-producer boundary and does not claim that
boundary's full-success status. Header unpacking and actual preparation,
assembly of greatest-strictly-earlier searches, and the complete producer's
native initialization, output, and total ledger are still needed. The report
uses the continuation provision for a verified partial, not the five-target
completion gate.

## Provenance and ownership

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Source branch checked out: `complexity/arora-barak-ch1`, never `main`.
- Observed source tip carrying the binding A3 brief:
  `651179be088f32530591f2f3ee65a28357a5caa1`.
- Required base, object-verified and used exactly:
  `2efe40c8a7b55e266d2ca1b8a558342479ef3123`.
- Working branch: `fill/ch2-e4-A3`, created at that required base.
- Delivery commit: **cd8eb55eb73aaf03bbf286b8464636988608dc24**.
- Delivery tree: **a72b02c4e394c0652c92b67fd99d9abd6d02c294**.
- Sole changed repository path: `TCSlib/Complexity/CookLevin/Hardness.lean`.
- No push, PR, or other branch modification. The source and remote-tracking
  branches remain at the observed source tip. Single-agent execution.

The A3 brief was read first from the committed source branch, followed by its
binding predecessors and their reports, especially A2's four-step frontier,
six-row boundary mapping, and inherited runtime facts. The policy/workflow,
phase-4 boundary resolutions and findings, emitter resolutions and stage-to-seam
mapping, and relevant native construction contracts were consumed. The external
prior-art Cook–Levin proof was not retrieved, imported, cited, or transcribed.

The source tip contains the A3 brief beyond the required base. The source
implementation and predecessor artifacts used here are the required-base
versions; the A3 brief is included separately in the ZIP.

## Targets in their required order

| Target | Status |
|---|---|
| `NPHard.polyTimeReducible` | Already proved; unchanged; empty admission roots. |
| `SAT_NPHard` | Original admission unchanged. Work remains inside continuation step 1. |
| `SAT_NPComplete` | Original admission unchanged; deferred until hardness closes. |
| `SAT3_NPHard` | Original admission unchanged; the proved `SAT_reducible_SAT3` dependency is separately checked clean. |
| `SAT3_NPComplete` | Original admission unchanged; deferred in order. |

The four owned roots are unfinished assigned work, not admitted dependencies
allowed inside completed proofs. The only out-of-scope source admission is
`TAUTOLOGY_coNPComplete`; it is untouched.

## What is newly banked

| Component | Exact new result |
|---|---|
| Native parallel counter bank | `clBank*` runs the inherited one-tape binary increment on selected disjoint tapes. Finished components stay idle; a complete product configuration is proved, and actual first completion is bounded. |
| Actual signed/clamped displacements | `clMoves_correct` uses the public virtual-input clamping theorem and actual source work moves. `clSelect`, `clAdvance`, and `clSigned_advance` select separate positive and negative movement counts; their difference equals the physical coordinate. `clTrack_round` executes the source action exactly once before counter administration. |
| Native field and row copying | `clCopy_run/first` writes doubled source bits and one aligned `01` delimiter onto the record tape, restores the source head, and preserves physical input/output. `clRow_stored/first` assembles the fixed field order with a charged dispatch between fields. |
| Actual stored inclusive trajectory | `clCounts_positions/schedule` identify counters with the public reference schedule. `clRec_prefix/complete` assemble row copying, unary-clock control, and source tracking into one actual native recorder. `clRec_complete` stores rows `0..T`, including time zero before any source step and time `T` after the last step. The full final source, counters, clock and record are specified. |
| Silence and recording ledger | `clRec_prefix_silent` proves every physical-output prefix through completion is empty. `clRec_cost_bound` bounds actual recording time independently of formula size; `clRec_bank` combines silence, the stored tape, and separate runtime/record-length bounds. |
| Exact stored format | `clRowPrefix_fields`, `clRecords_fields`, and `clReadFields_row/records` prove the stored word decodes into every canonical counter field in exact row order, retaining an arbitrary suffix. These are pure format theorems, not native random-access claims. |
| Native signed-position comparison | `clCmp_run/first` scans four binary words in lockstep, compares their two cross-sums using finite carries, rewinds every head, and returns the exact Boolean verdict. `clSigned_compare` and `clSchedule_compare` identify it with signed-coordinate equality and with the public work-head schedule. The first-return guard excludes both possible completed verdicts. |
| Native sequential field reading | `clRead_run/first` consumes exactly one encoded field, overwrites its target, preserves the full stream, advances to the next field, and restores the target head. Its old-target-length precondition is explicit. `clCounts_width_mono` discharges that precondition while visiting a movement-count field in increasing source-time order. |

There is one new contiguous private block. All 129 inherited private
statements, definitions, proofs and docstrings remain byte-for-byte unchanged.
None of the inherited arithmetic, reference, counter, or emitter results is
replaced or re-proved as an alternative interface.

## Stored representation and its limits

For a fixed source machine with `k` work tapes, each row has
`l = 2*(k+1)` binary fields. The first `k+1` fields count actual positive
moves; the second `k+1` count actual negative moves. Coordinate zero denotes
the virtual input head; the remaining coordinates denote source work heads.
Every count uses canonical little-endian `Nat.bits` and the inherited
self-delimiting `pairEncode` field format. Rows are concatenated in increasing
time order. Row time is implicit in its place in that sequence.

A work position is positive-count minus negative-count. The input coordinate
is the shifted input position minus one; `clCounts_schedule` recovers the
public input position by adding one. Requested outward input moves are
clamped before choosing a counter, so boundary attempts do not create fictitious
movement. Counts start at zero and remain frozen after internal halt, as
`clCounts_halted` states. The source's effects-first terminal transition is
still executed by the inherited `clRefAction` before any administrative step.

Two count pairs can represent the same signed position despite different
words. `clSigned_eq` therefore compares cross-sums, and the native comparator
really computes those sums column by column. It never substitutes equality
of raw encodings for equality of positions. The maximum word width appears
only in the proof of its scan bound; the machine detects actual tape blanks.

The reader's overwrite contract requires the old target word to be no longer
than the new field. This includes initially blank targets and successive
movement-count rows, by `clCounts_width_mono`. **Restarting a search at the
initial row requires an explicit target reset/cleanup or a suitable new
loader contract.** No unproved reset or row-loader loop is silently assumed.
The reader consumes the stream in order and charges each stream-bit read;
its pure decoder companion does not provide free indexed access.

## Six-row contract and boundary-check mapping

| Stage | Discharge in this checkpoint and exact remaining boundary |
|---|---|
| s1 — exact arithmetic | The untouched `clNPVerifier` and `clPrepHeader_native/machine` retain the instance and exact certificate/reference/horizon values, including zero coefficient/degree cases and complete captured answers. **Open:** integrate header parsing, retained data and administration into the complete record producer. `clRead_first` is an actual field-reader component, not an assembled header unpacker or silent preparation return. The header alone is still not the packed result. |
| s2 — reference simulation | `clTrack_source/round` consume `clRefAction` and its whole-configuration proof. `clCounts_positions/schedule` identify the stored coordinates with the literal source run and public all-false reference schedule. `clRec_prepared` states the exact prepared `Cfg.ofWords` seam with blank source tapes, initial source state, virtual-input origin, counters, record and unary clock. **Open:** actually produce that layout from the header/native input, retaining all required instance/header fields. Neither `clRec_prepared` nor the inherited prepared seams is a genuine native `initCfg` startup proof. |
| s3 — output and halting | The actual recorder uses the silent inherited reference action, retains source halting internally, and performs terminal writes/moves before counter work. `clRec_prefix_silent/bank` prove empty physical output through the whole recording run, including administrative steps. `clCounts_halted` freezes later counters. **Open:** extend this isolation invariant across header preparation, all last-visit searches, packing and complete-producer return. No complete assembled producer is claimed. |
| s4 — inclusive trajectory | **The A2 running-invariant-to-stored-word gap is now discharged from the prepared seam.** `clMoves_correct`, `clSigned_advance`, `clCounts_positions`, and `clRec_prefix/complete` prove actual signed/clamped tracking and a stored row at every time `0..T`. Rows are copied before the clock test: the initial and final rows are included. `clRec_copy` frames the entire source; `clRec_advance` executes exactly one source transition after the administrative phase; `clRec_complete` specifies all final tapes/heads. `clReadFields_records` proves exact field recovery. **Open:** integrate the retained header and establish the actual native preparation/startup, then use these rows in the complete producer. |
| s5 — greatest earlier visits | `clSchedule_compare` is a proved native equality call for two stored signed work positions, and `clRead_first` provides charged sequential field access with an explicit overwrite precondition. **Still open:** assemble the row loader and scan all and only `s<t`, track the greatest matching time or `none`, store its encoding, prove the empty time-zero case and immediately preceding frozen-visit case, reset scratch between queries, and charge every copy, comparison, scan, dispatch and cleanup in the whole search/producer ledger. No new complete native last-visit search is supplied; the inherited `clPrev_spec` is unchanged. |
| s6 — serialization | The 77 inherited pure-layer declarations, fixed templates, exact clause/literal ledger, `clTableau_chunks`, and `clEmitter_of_body` remain unchanged. **Open:** the ordered round controller, cursor updates, all clean positive returns (including empty and saturated cases), fuel, one common polynomial budget, and its actual application. No emitter body or output identity is newly claimed. |

**Packed-records install:** no new install-call instantiation is made. The
complete producer must include the trajectory and greatest-earlier records;
the exact arithmetic header is not substituted at the final install bridge.

**Genuine startup:** still open, including retained instance and every
administrative tape/head at the whole canonical `Cfg.ofWords` seam. The new
recorder's prepared seam is not a native `initCfg` proof.

**Common budget versus horizon:** the recording bounds below do not provide
the emitter's common polynomial `P`. That future bound must cover startup,
fuel and every whole round; it is not the source horizon `T`.

**Output identity before semantics:** neither stage is discharged here.
The future controller must instantiate `clEmitter_of_body` and
`clTableau_chunks` first. Pure equisatisfiability then uses certificate pinning,
strong induction over time with the public snapshot APIs and bitwise product
slices, and the total decider's exact singleton output at the horizon.
No decoded-equality substitute, consistency-clause redesign, or false
reference-output prefix has been introduced.

The protected family order, last-index-versus-member-count distinction
`R`/`R+1`, and single-final-terminator chunk rule are unchanged.

## Runtime facts actually proved

The A2 header, bare reference runner, increment, framed increment and binary
width ledgers are inherited unchanged. The following are new native facts;
none is inferred from the quadratic formula-output bound.

| Component | New proved bound or exact cost |
|---|---|
| Parallel selected increment bank | Completion within `2W+2`, where all starting counter widths are at most `W`. Parallel native tapes justify the maximum-width bound. |
| Tracking round | `clTrack_round`: positive duration at most `2W+4`, including the actual source action and return dispatch. |
| Tracking without recording | `clTrack_schedule`: through `T` source steps within `T*(T+3)`, with exact final source and signed counters. |
| One encoded field copy | `clCopy_run`: exactly `3*|w|+3`; `clCopy_first` cuts to a positive actual first return. Empty fields take three steps. |
| One row | `clRow_stored/first`: at most `l*(3W+4)`, including one dispatch per field. |
| Recorder's clock/source phase | One charged clock tick; `clRec_advance` at most `2W+5`, including the final dispatch back to row copying. The final blank-clock stop is also charged. |
| Inclusive stored recorder | `clRec_complete`: at most `(T+1)*(l*(3T+4)+2T+7)` from its prepared seam. `clRec_cost_bound/bank`: at most `(4l+7)*(T+1)^2`. All copied rows, source steps, counter work and recorder dispatches are included. |
| Stored record length | `clRecords_length/bank`: at most `2l*(T+1)^2` bits for the inclusive trajectory. This is a separate storage bound. |
| Four-word comparison | `clCmp_run`: exactly `2L+2`, with `L` the maximum actual input-word width; positive first return at most `2W+2` if each width is at most `W`. All words survive and all heads return to zero. `clSchedule_compare` gives `2T+2` for times at most `T`. |
| Sequential field reading | `clRead_run`: exactly `3*|w|+3` under its explicit old-target-length precondition; `clRead_first` gives the positive first return. This counts both encoded bits per field bit, the separator and target rewind. |

**Not proved:** a complete row-loader/search ledger, whole packed-producer
runtime from genuine native input, whole startup, common emitter budget,
or reduction runtime. All such costs remain named obligations.

## Exact continuation frontier

Continue the binding four-step plan, still inside step 1:

1. **Finish the complete packed-record producer.** Unpack the inherited exact
   header into an actual retained-instance/clock/reference layout. Consume
   the new native recorder rather than re-establishing its stored trajectory.
   Assemble a sequential row loader and the greatest-strictly-earlier search
   using the native reader/comparator, with explicit scratch resets and
   candidate-time/last-match storage. At time zero inspect no rows; for a
   frozen time use the immediately preceding equal-position visit. Prove
   full packing/output from native input and a total ledger covering every
   comparison, scan, dispatch, record copy and cleanup. The complete producer
   and that total ledger remain the natural checkpoint.
2. **Install the complete packed result, then genuine startup.** Use that
   completed producer at the install bridge, retain the instance, add the
   bounded emission cursor, and prove the entire canonical `Cfg.ofWords`
   seam from native `initCfg`, including all administrative buffers and heads.
3. **Build ordered emission.** Use the protected fixed finite tables and
   exact `clChunk` order. Prove all positive first returns, complete scratch
   restoration, cursor updates, a positive silent saturated round, fuel,
   and one common polynomial `P` for all startup/fuel/round work.
4. **Prove output identity before semantics.** Instantiate
   `clEmitter_of_body` and `clTableau_chunks`, then prove pure
   equisatisfiability by pinning recovery and the specified strong induction
   using the public snapshot APIs and bitwise product slices. Use the exact
   singleton decider output at the horizon, then close `SAT_NPHard` and its
   corollaries in order. All newly closed targets must have empty admission
   roots; `SAT_reducible_SAT3` is already proved.

No statement obstruction was found. **Escalations: none. Requested shared
lemmas: none.** No unproved new helper or construction assumption is delivered.

## Freeze, provenance and style

`verify-freeze.py` deletes exactly the new contiguous block and recovers the
entire required-base source **byte for byte**. It also compares the source
blocks of all **129 inherited private names** and records their hashes;
the name-level diff is empty. All five public statements/proofs, every
inherited docstring, imports, options, and declaration order are untouched.
Every new source and generated kernel declaration is private.

The product counter bank is locally adapted from `emitterBank*` in the
committed `Build/Primitives.lean`: the component is the inherited one-tape
increment, with selected idle/carry starts. The local `clSlot*` relocation
helpers are harvested from that file's `emitterP2*` relocation construction;
their private names are local to this owned module. The native copy, tracking,
recording, arithmetic comparison and field-reader controllers have their own
complete-configuration proofs. No cross-file private declaration is cited.
The inherited counter implementation is not changed.

Final source: **4471 lines, 229545 bytes**; **2359 insertions,
zero deletions**. SHA-256: `a26f33c3a56422127c7f01ab34bd32290cccdce82c12231c87c189d5d67f7815`.
The recorded file-size exception continues: exclusive ownership requires
these helpers to remain private in `Hardness.lean`; splitting another module
would violate the brief. Nontrivial new proofs have adjacent English sketches.
Style lint over the CookLevin subtree reports 0 FAIL and the one documented
Hardness file-size WARN.

## Verification

| Gate | Final result |
|---|---|
| Fresh ordered sweep | **57/57**, exit 0, zero `error:` diagnostics, 57 fresh nonempty oleans. |
| Admission diagnostics | Exactly **5**: four untouched owned targets and the untouched out-of-scope `TAUTOLOGY_coNPComplete`. |
| Kernel closure traversal | **PASS** over all **757** owned checked kernel declarations, including generated declarations. All **279** private source declarations (129 inherited + 150 new) are admission-free, with at most `propext`, `Classical.choice`, `Quot.sound`. |
| Public targets | Target 1 clean; each of the four unfinished targets retains exactly its own admission root. `SAT_reducible_SAT3` is separately printed and checked clean. |
| Dependency regressions | Emitter loop, both clean-call bridges, exact polynomial-bit evaluator, oblivious normalization, snapshot locality and SAT/SAT3 membership all checked clean. |
| Public surface | **PASS**: exactly the five original public declarations; every addition, including generated declarations, is private. |
| Source freeze and ownership | **PASS**: byte-for-byte baseline reconstruction; empty name-level diff over all 129 inherited privates; only `Hardness.lean` differs; clean committed working tree. |
| Style | 0 FAIL, one recorded size WARN over the CookLevin subtree. |
| Transport | Patch replay reproduces the committed tree exactly; incremental bundle verifies; archive is flat and every manifest checksum passes. |

The traversal reads checked kernel types and opaque values, follows inductive
constructors, explicitly rejects missing checked declarations, and separately
checks permitted axioms. Its expected admission roots describe a partial
checkpoint. This is **not** a pass of the five-target completion gate.

The bootstrap compiled all 49 prerequisites before encountering the owned
in-progress block; the later corrected owned module and downstream modules
passed. The initial failed iteration is retained as `bootstrap.log`, not
presented as successful final verification. The final sweep used an independent,
initially empty output tree and checked the final owned source plus all later
modules. The public-surface audit initially caught equation lemmas generated
for imported schedule definitions; direct `delta` unfolding removed that
unintended surface without changing any statement or imported definition.
The final kernel and surface audits were rerun against the final fresh oleans.

Final sweep tail:

```text
TCSlib/Complexity/CookLevin/Hardness.lean:4462:8: warning: declaration uses 'sorry'
TCSlib/Complexity/CookLevin/Hardness.lean:4468:8: warning: declaration uses 'sorry'
CHECK 51/57 TCSlib/Complexity/ClassNP/Tautology
TCSlib/Complexity/ClassNP/Tautology.lean:1271:8: warning: declaration uses 'sorry'
CHECK 52/57 TCSlib/Complexity/TuringMachine
CHECK 53/57 TCSlib/Complexity/ClassP
CHECK 54/57 TCSlib/Complexity/Uncomputability
CHECK 55/57 TCSlib/Complexity/Formulas
CHECK 56/57 TCSlib/Complexity/CookLevin
CHECK 57/57 TCSlib/Complexity/ClassNP
FULL_SWEEP_COMPLETE 57/57 2026-10-06T05:43:21.189914+00:00
```

Final kernel traversal result:

```text
CHECKPOINT_AUDIT_PASS: 279 source private declarations; 757 owned kernel declarations including generated declarations; all inherited and new helpers admission-free; all five public targets unchanged, with exactly the four original later targets open; SAT_reducible_SAT3 clean. This is not the five-target completion gate.
```


## New private declaration inventory

All names are private in `Complexity`:

```text
clBankPart
clBankTM
clBankCfg
clBank_part
clBank_step
clBank_run
clBankStart
clBank_component
clBank_finish
clBank_idle
clBank_first
clMoves
clPositions
clMoves_correct
clSelect
clAdvance
clSigned
clSigned_advance
clAdvance_bound
clSigned_eq
clTrackTM
clTrackCfg
clTrack_source
clLeft_until
clTrack_frame
clTrack_dispatch
clTrack_round
clBuffer_append_bit
clTwo
clCopyTM
clCopyCfg
clCopy_write
clCopy_pair
clCopy_forward
clCopy_separator
clCopy_rewind
clCopy_run
clCopy_idle
clCopy_first
clSlotAction
clSlotCfg
clSlot_apply
clSlot_run
clRowIndex
clRowSelect
clRow_inverse
clRowTM
clRowCfg
clRow_frame
clRow_field
clRowPrefix
clRow_prefix_run
clRow_stored
clRow_idle
clRow_first
clRowPrefix_length
clElapsed_width
clTrack_schedule
clTag
clTag_valid
clMove_inj
clMoves_tag
clCounts
clCounts_succ
clCounts_bound
clCounts_positions
clRecFields
clRecords
clRecState
clRecTrackIndex
clRecTrackSelect
clRecRowIndex
clRecRowSelect
clRecTrack_inverse
clRecRow_inverse
clRecClockIndex
clRecTM
clRecCfg
clRec_row_frame
clRec_row_inactive
clRec_copy
clLeft_ne_right
clRight_ne_left
clRec_tick
clRec_stop
clRec_track_frame
clRec_track_inactive
clSlot_release
clRec_advance
clRec_prefix
clRec_complete
clRec_prepared
clRec_prefix_silent
clRec_cost_bound
clBit
clNum
clNum_bits
clNum_head
clAddColumn
clAddColumn_value
clCmpUpdate
clCmpPred
clCmpUpdate_spec
clCmpOrbit
clCmpOrbit_spec
clCmpSize
clCmp_width
clCmp_blank
clCmpVerdict
clBit_eq
clCmpVerdict_spec
clCmpTM
clCmpCfg
clCmp_read
clCmp_forward_step
clCmp_forward
clCmp_finish_scan
clCmp_rewind
clCmp_run
clCmp_idle
clCmp_first
clSignedWords
clSigned_compare
clCounts_schedule
clCounts_halted
clFields
clPair_append
clFields_append
clRowPrefix_fields
clReadFields
clReadFields_fields
clReadFields_row
clReadTM
clReadCfg
clRead_pair
clRead_forward
clRead_separator
clRead_rewind
clRead_run
clRead_idle
clRead_first
clCountInc_nondecreasing
clCounts_width_mono
clRecordFields
clRecordFields_length
clRecords_fields
clReadFields_records
clRecords_length
clRec_bank
clSchedule_compare
```

## Delivery and reproduction

The flat **`fill-ch2-e4-A3.zip`** contains this report, full `Hardness.lean`,
the format-patch series, an incremental git bundle, final fresh sweep and
kernel/axiom-print logs, freeze and public-surface evidence, the private
inventory, dependency/toolchain records, reproduction scripts and root
`SHA256SUMS`. The full source maps to the sole owned repository path stated
above. The bundle requires the exact recorded base.

Verify the extracted contents with `sha256sum -c SHA256SUMS`. Apply the patch
on a maintainer-chosen branch containing the base. `RUN_CHECKS.sh` accepts
the repository path and a new absolute verification directory; with the
pinned runtime and dependency cache available it runs the ordered sweep,
closure traversal, public-surface check and exact source-freeze check.

`lake exe cache get` was run exactly once and succeeded, unpacking 7,506
matching cached files. No `lake build` ran. All 11 materialized dependency
checkouts match their manifest pins with no tracked changes. The four
unmaterialized documentation-generation packages are explicitly recorded;
they are not dependencies of the required 57-module source sweep.

The stock Lean 4.25.0 runtime uses the inherited process-path compatibility
shim, whose source is included: it maps only the current process's numeric
executable-path lookup to `/proc/self/exe`. Compiler/kernel bytes are unchanged;
ordinary runtimes need no shim.

**Notation:** `x` is the original/native instance; `y` is the represented
source input (specialized to the all-false word for the public schedule);
`M` is the fixed source verifier; `k=M.k`; `l=2*(k+1)` is the row field count;
`m` is the reference-input length; `T` is the source horizon; `W` is a common
binary field-width bound; `L` is a comparison's actual maximum width; `w` is
one binary word and `|w|` its length; `s,t` are source times where stated;
`R` is the inherited last round index and initial fuel; `P` is the still-open
common emitter budget, distinct from `T`. Positive and negative move counts
are separate nonnegative integers; their difference represents a signed
coordinate.
