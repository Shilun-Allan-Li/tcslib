# W1 record tables — continuation 2, partial delivery

**0 of the 6 requested public rows is newly closed.** The file remains at
**14 of 20 original targets proved**. This continuation proves the finite
table-find round and its clocked interface, with **20 new private declarations**
and no new admissions. The complete table-find wrapper is unfinished; append
and the four record-machine rows retain their original bodies and sketches.

This is the explicit partial-delivery option in ground rule 9. No public
admission was moved into a helper. **Private helpers remaining `sorry`: none.
Proved-modulo targets: none.** No unfinished public row is presented as proved.

## Base, branch, and scope

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Campaign branch: `complexity/arora-barak-ch3-4`; `main` was never checked out.
- Base: `3462c1b49a49d2cd458f595624c1dbac1f868af3`.
- Working branch: `fill/w1-recordtable-cont2`, created directly from that base.
- Required ancestor: `13957bf73eb37763259be1fd01a5cca9bd03c21f`.
  `git merge-base --is-ancestor` succeeded before any proof work.
- The committed continuation-2 brief was read first. Its named predecessor
  reports, earlier briefs, design, policy, workflow, and audit guidance were read.
- Only tracked changed path:
  `TCSlib/Complexity/TuringMachine/Build/RecordTable.lean`.
- Delivery commit: `3f80dd136132ee9a3ad7c72b5756c528a2d7cceb`.
- No rebase, push, PR, or change to another branch.

Between the required ancestor and the base, only campaign documents and briefs
changed. No Lean source, warning inventory, or screening population changed.
The recorded baseline has 18 admitted declarations: the six owned rows and
the 12 out-of-scope declarations listed below. There is no parallel-fill
difference at this base.

## Target status

| Row | Target, with `Turing.` prefix | Status |
|---|---|---|
| 15 | `exists_tableFindTM` | Admitted; finite field round, first-exit contracts, and proof-clock interface proved |
| 16 | `exists_tableAppendTM` | Admitted; inherited `rt_append_copy` prefix unchanged |
| 17 | `exists_recordTemplateTM` | Admitted; original sketch retained |
| 18 | `exists_recordInitTM` | Admitted; original sketch retained |
| 19 | `exists_recordValidTM` | Admitted; original sketch retained |
| 20 | `exists_recordNextTM` | Admitted; original sketch retained |

Work stopped at row 15, preserving the required order. Rows 16–20 were not
attempted in this continuation. All six bodies remain their original explicit
admissions, each with its literal “Proof sketch”. All 14 proved target bodies,
all 13 inherited private declarations, and every other inherited body are
unchanged. Public names, order, signatures, docstring text, and imports are frozen.

## New private declarations

Counts below concern explicit source declarations; the inductive also generates
its ordinary recursors and deriving instances.

| Declaration | Role |
|---|---|
| `rt_findPhase` | Finite field-round phases: entry observation, indexed scan, indexed skip carrying the accumulator, and escape; derives `Fintype` and `DecidableEq`. |
| `rt_findControl` | Selects the existing control type for each phase. |
| `rt_findControl_fintype` | Finite control-family instance. |
| `rt_findControl_decidableEq` | Decidable control-family equality. |
| `rt_findParts` | Catalog fold scans and skips, plus a stationary one-cell observation and exit phase. |
| `rt_findRedirect` | Finite field counter and accumulator dispatch; accepts before the final skip. |
| `rt_findRound` | Instantiates the public `phaseHostTM`; it is the body intended for `counterLoopTMVia`. |
| `rt_find_scan` | Specializes `scanTM_run_ofCfg` and `scanResult_fold` to a read-only fold, simplifying its write mask to the original tape. |
| `rt_find_fold_cons` | Splits the layout fold into a word fold, its separator, and the remaining fields. |
| `rt_find_read` | Exact one-step observation and second-step dispatch, without tape or head changes. |
| `rt_find_scan_phase` | Hosted catalog scan through its first exit and one dispatch. |
| `rt_find_skip_phase` | Hosted catalog skip through its first exit and one dispatch. |
| `rt_find_last_accept` | Accepted final field escapes before its skip, with exact time, cut, and head interval. |
| `rt_find_advance` | Shared scan-and-skip segment for a nonfinal field or a rejected final field. |
| `rt_find_fields_run` | Composes the existing phase contracts across the remaining fields, with exact endpoint and a linear time bound. |
| `rt_find_blank` | A blank entry cell escapes in two stationary steps with the required intermediate cut. |
| `rt_find_entry` | Complete nonempty-entry round: positive time, first-return/escape cut, exact frame. |
| `rt_findClock` | Proof-only first positive entry/escape time; absent from the executable transition table. |
| `rt_findClock_eq` | Identifies that clock using a concrete endpoint and no-earlier-anchor cut. |
| `rt_find_round_entry` | Exposes the entry-round result on the actual hosted configuration at that proof clock, ready for the public counter-loop orbit. |

The phase transitions use the public scanner, skipper, and finite phase host.
No second scanner, copier, loop host, seam trace, or field-layout induction is
introduced. `rt_find_fields_run` is an induction composing field-controller
segments; its frame restriction cites the public layout lemmas.

All 20 new declarations have axiom closures contained in `propext`,
`Classical.choice`, and `Quot.sound`.

**Requested shared lemma:** promote/generalize Catalog's private, Bool-only
`f2_head_steps` to arbitrary tape alphabets and state universes, bounding each
work head's displacement from its entry position by elapsed time. A general
version was prototyped here, then removed when the existing private fact was
identified. No copy of that argument or new generic radius lemma is shipped.
A future continuation can instead compose the existing phase trajectory bounds.
No shared file is changed here.

## The proved round

The controller tests the current entry cell, folds each word with the catalog
scan, and applies the separator transition exactly between consecutive fields.
A rejected final field is skipped, returning to the round entry at the next
entry offset. An accepted final field dispatches directly to escape while its
head is still at that field's start. Well-formed table entries make that cell
nonblank. Thus the accepted-last-entry case retains the required distinguishing
cell; the blank end-of-table case escapes without moving.

For a nonempty `m`-field entry `fs`, the round costs at most
`7 * ((joinFields fs).length + 1)`. Every earlier positive time is live and
avoids both the entry and escape anchors. The exact endpoint preserves every
tape, the other work head, input position, and output. The work-head radius
remains part of the full wrapper proof. The accepted-final-field segment
retains the catalog's explicit head interval. Each catalog exit is intercepted
at its contract's exit time, followed by one public-host dispatch.

The proof clock is not an executable oracle. The transition table only uses
finite control and tape symbols; the clock merely supplies the `τ` parameter
for the existing `counterLoopOrbit` proof interface.

## Continuation frontier

1. Resume row 15 with `rt_findRound hm δ a₀ acc` as the two-tape body and
   `rt_findClock hm δ a₀ acc` as its proof clock. Its anchors are
   `⟨.read, none⟩` and `⟨.exit, ()⟩`. `rt_find_round_entry` supplies the exact
   entry round on the hosted state type; `rt_find_blank` and `rt_findClock_eq`
   supply the two-step terminal blank round.
2. Prove the table-index orbit up to the first accepted entry, or to
   `es.length` if none accepts. Use `TableAt.recordAt_take` for each entry and
   `tableOffset_length` for the final blank. Instantiate the public
   `counterLoopTMVia_run_escape`; do not build another loop or orbit trace.
   The last round index is at most `es.length`, strictly below the fuel value.
3. Sum the round bounds and use `counterOverhead_le_of_le`. Preserve the
   distinction between the count of rejected entries and the additional
   accepted/blank escape round. The brief's warning about big-operator
   precedence still applies.
4. Compose the prefix: copy the original fuel on tape 1 to blank scratch tape
   2 with `copyTM`, then skip the header on tape 0. The rich loop has the
   existing two body tapes plus its counter tape. The original fuel remains
   untouched by the loop.
5. At escape, read the current table cell to distinguish acceptance from the
   final blank. For acceptance, the scan already restored the final field's
   head, so exactly `m - 1` backward skips return to the accepted entry's
   first field. For no match, apply `tableRewindTM_run_ofCfg`. Clear the
   scratch counter using its preserved width and frame, and restore every
   other component before the distinct verdicts. Intercept each submodule exit.
6. Package the finite state witnesses and uniform linear constant, including
   the final work-head radius. Compose the public phase/loop trajectory bounds,
   or use the shared general head-displacement promotion requested above if it
   has landed. Find and append permit a radius equal to their time budget.
7. Then resume row 16 from the frozen `rt_append_copy`. Its destination head
   is the old second trailing blank, the source tape/head and other components
   are restored, and the copied layout is already present. For empty suffix,
   attach the old-table rewind directly; for nonempty suffix, cross the copied
   fields, write the suffix, and return. The rewind frame excludes its current
   cell. New fields may be empty: the append contract does not preserve
   `TableWF`, and later seekers must ensure their required nonemptiness.
8. Continue rows 17–20 in order: the proved input-length row, increment plus
   one-cell overflow extension, dedicated digit tapes, initial-field writes,
   validity's lifted counter loop, and the odometer under the rich loop.
   The native-input and empty-tag obligations remain exactly as issued.

**Escalations: none.** The inherited universe obstruction is resolved in the
base; no signature change is requested or made. This delivery stops for the
continuation budget, not because the remaining statements have been shown false.

## Documentation and freeze

The only inherited docstring addition is the flagged **“Fill appendix
(continuation 2, partial)”** on `exists_tableFindTM`. It records the proved
round and the unfinished wrapper. All original sketch and attribution text
is retained. Status and Main results text are unchanged because the public
completion count is unchanged. **Imports: unchanged.**

The mechanical freeze audit compares inherited declaration order, public
visibility and signatures, every frozen body, all original docstrings, and
the import list. It also checks the sole tracked path and `git diff --check`.
Final source size: **2,470 lines; 28 public / 33 private explicit declarations**.

## Verification

All Lean checks used `scripts/lean_check_tree.sh`; no `lake build` was run.
Lean is pinned to 4.25.0 and mathlib to
`029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`. The dependency manifest and
mathlib checkout were verified. A targeted `lake exe cache get` for the exact
external imports succeeded (`logs/cache-targeted.log`).

The unchanged baseline and the final ordered sweep each completed with
**exit 0, 88/88 modules, zero errors, and exactly 18 sorry warnings**. These
are the same six unfinished owned rows plus the same twelve out-of-scope
declarations. The installed owned file has exactly those six warnings and
no others. No new helper is admitted.

The sweeps emitted separate fresh olean trees. The final sweep's 83 unchanged
upstream modules ran first; its last five modules ran after installation of
the final source. All evidence modules were then checked on that same final
tree. Development objects were not substituted into the final sweep.

The unchanged out-of-scope admissions are:

| Module | Names |
|---|---|
| `Build/OracleSim` | `FinOracleTM.exists_plain_simulation` |
| `CodeSimulator` | `exists_polyCanonizer`, `exists_uniformSimulator` |
| `Diagonalization/EXPCOM` | `NPOracle_EXPCOM_subset_EXP` |
| `Diagonalization/NTimeHierarchy` | `exists_timed_universal_NDTM`, `exists_ndAcceptsWithin_decider`, `exists_codeNDTM_accepts_linear`, `ntime_hierarchy`, `ntime_hierarchy_of_pos`, `NTIME_linear_ssubset_square` |
| `Build/Zone` | `exists_zoneShiftInTM`, `exists_zoneShiftOutTM` |

`logs/axiom-print.log` contains every original target's axiom print (20),
plus `RecordValid.joinFields_length`. Only the six explicitly unfinished rows
contain `sorryAx`. `logs/private-axioms.log` prints all 20 new private
declarations: no `sorryAx` and no nonstandard axioms.

| Executed evidence | Outcome |
|---|---|
| `S128bStatementsProbe.lean` | Exit 0, no errors/warnings; byte-identical to the issued evidence; both last-match and empty-field-append cases retained |
| `EmptyTagProbe.lean` | Exit 0, no errors/warnings; empty-tag validity, empty enumeration, computed `no` branch, and zero-time controller |
| `FindRoundProbe.lean` | Exit 0, no errors/warnings; accepted only field, rejected field, blank entry, and two-field accepted-last case; exact times 7, 10, 2, and 17 |

The empty-tag case executes `decide`/`rfl` as required by note 50. It checks
the empty-enumeration boundary and does not prove the still-admitted general
`exists_recordNextTM`. The four round cases execute the actual new machine
from `RecordTable`, using a private-name syntax macro only to expose it to
the evidence module.

The style lint ends with `style_lint: 0 FAIL, 9 WARN over 20 files`; all nine
warnings concern file size. The owned file's size is permitted by note 46.
The mechanical verification summary is:

```text
bootstrap.log: 88 modules; 0 errors; exactly 18 admitted declarations
final-sweep.log: 88 modules; 0 errors; exactly 18 admitted declarations
Owned admissions: six unchanged targets; out-of-scope admissions: twelve unchanged
Admission names:
  Diagonalization/EXPCOM: NPOracle_EXPCOM_subset_EXP
  Diagonalization/NTimeHierarchy: NTIME_linear_ssubset_square
  Diagonalization/NTimeHierarchy: exists_codeNDTM_accepts_linear
  Diagonalization/NTimeHierarchy: exists_ndAcceptsWithin_decider
  Diagonalization/NTimeHierarchy: exists_timed_universal_NDTM
  Diagonalization/NTimeHierarchy: ntime_hierarchy
  Diagonalization/NTimeHierarchy: ntime_hierarchy_of_pos
  TuringMachine/Build/OracleSim: exists_plain_simulation
  TuringMachine/Build/RecordTable: exists_recordInitTM
  TuringMachine/Build/RecordTable: exists_recordNextTM
  TuringMachine/Build/RecordTable: exists_recordTemplateTM
  TuringMachine/Build/RecordTable: exists_recordValidTM
  TuringMachine/Build/RecordTable: exists_tableAppendTM
  TuringMachine/Build/RecordTable: exists_tableFindTM
  TuringMachine/Build/Zone: exists_zoneShiftInTM
  TuringMachine/Build/Zone: exists_zoneShiftOutTM
  TuringMachine/CodeSimulator: exists_polyCanonizer
  TuringMachine/CodeSimulator: exists_uniformSimulator
Public axioms: 20 targets + one derived corollary; sorryAx only on the six unfinished rows
New private axioms: 20 declarations; standard axioms only; zero admissions
preship-probe.log: no errors or warnings
empty-tag-probe.log: no errors or warnings
find-round-probe.log: no errors or warnings
style_lint: 0 FAIL, 9 WARN over 20 files
Fresh final olean files: 88/88
Preship probe is byte-identical to the committed evidence source
All 24 final source files are byte-identical to the immutable after-screen snapshot
```

Final sweep tail:

```text
CHECK TCSlib/Complexity/TuringMachine/Build/Zone
TCSlib/Complexity/TuringMachine/Build/Zone.lean:1110:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Zone.lean:1146:8: warning: declaration uses 'sorry'
CHECK TCSlib/Complexity/TuringMachine/Build/InputLength
CHECK TCSlib/Complexity/TuringMachine/Build/RecordTable
TCSlib/Complexity/TuringMachine/Build/RecordTable.lean:1924:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/RecordTable.lean:2198:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/RecordTable.lean:2250:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/RecordTable.lean:2301:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/RecordTable.lean:2359:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/RecordTable.lean:2420:8: warning: declaration uses 'sorry'
CHECK TCSlib/Complexity/TuringMachine/Build/CertShell
TCSlib/Complexity/TuringMachine/Build/CertShell.lean:184:4: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
CHECK TCSlib/Complexity/TuringMachine/Robustness/Bidirectional
CHECK TCSlib/Complexity/TuringMachine/Codes2Tape
CHECK TCSlib/Complexity/TuringMachine
```

For this runtime only, the included `self-exe-compat.c` redirects Lean's
`readlink` of `/proc/<its-own-pid>/exe` to the equivalent `/proc/self/exe`;
every other call is delegated unchanged. The later checks use a wrapper
passing `--threads=1` to the pinned Lean binary to reduce resource pressure.
Neither the kernel, binary, check script, nor trust options were modified.
The shim source, one-worker wrapper, and observed environment are included;
ordinary environments do not need the shim. An initial disconnected execution
service and slow concurrent elaboration consumed part of the continuation
budget; both required sweeps nevertheless completed successfully.

## Duplication gate

The exact 24-file population is `verification/screen-population.txt`. Both
full runs used the unchanged prescribed `copy-text-screen.py`. The before
output is byte-identical to the committed continuation-2 screen base.

Before (complete output: `logs/screen-before.txt`):

```text
declarations screened: 1477; copy pairs (target reproduces >= half of source): 1747; reproduced text: 582,620 chars
```

After (complete output: `logs/screen-after.txt`):

```text
declarations screened: 1495; copy pairs (target reproduces >= half of source): 1749; reproduced text: 583,308 chars
```

The after-screen ran on an immutable copy of precisely those 24 files. Their
SHA-256 manifest was checked against the final repository source before
delivery. No other batch's work was included.

```text
Before: declarations screened: 1477; copy pairs (target reproduces >= half of source): 1747; reproduced text: 582,620 chars
After: declarations screened: 1495; copy pairs (target reproduces >= half of source): 1749; reproduced text: 583,308 chars
Added pairs: 2; removed: 0; changed: 0
New owned cross-file pairs: 0; new owned in-file pairs: 2
New pairs at the 90% threshold: 0
   RecordTable.lean::rt_find_scan_phase  reproduces  RecordTable.lean::rt_find_skip_phase: 344/508 = 68%
   RecordTable.lean::rt_find_skip_phase  reproduces  RecordTable.lean::rt_find_scan_phase: 344/572 = 60%
new copies: none
```

Every new in-file pair is justified below. There are no new owned cross-file
pairs, no new pair at 90% or above, and no removed or changed inherited pairs.

| Directed pair | Measured overlap | Justification |
|---|---|---|
| `RecordTable.lean::rt_find_scan_phase` → `RecordTable.lean::rt_find_skip_phase` | 344/508 = 68% | Both specialize the public phase-host contract. Scan and skip require different catalog rows, control families, endpoints, and cuts; their shared hosting argument is already factored in `phaseHostTM_run`. |
| `RecordTable.lean::rt_find_skip_phase` → `RecordTable.lean::rt_find_scan_phase` | 344/572 = 60% | Both specialize the public phase-host contract. Scan and skip require different catalog rows, control families, endpoints, and cuts; their shared hosting argument is already factored in `phaseHostTM_run`. |

**new copies: none.** No duplication exception is requested. The inherited
copier pairs remain unchanged. The generic head-displacement prototype was
removed, as explained in the shared-lemma request above.

## Delivery and replay

- The full modified source is under its repository-relative `TCSlib/` path.
- `patches/` contains the one-commit `git format-patch` series against the
  recorded base. Its application to an isolated temporary index reproduces
  exactly the delivery commit's tree (`logs/patch-check.log`). No other
  working branch was checked out for this test.
- `fill-w1-recordtable-cont2.bundle` carries the same commit and working
  branch, with the recorded base as its prerequisite. Verification and the
  advertised branch are recorded in `logs/bundle-verify.log`.
- `logs/` contains the complete baseline/final sweeps, axiom prints, all
  final probes, style lint, freeze/scope checks, both full duplication screens,
  their delta, and mechanical verification summary. Failed development drafts
  and interrupted runs are excluded.
- `verification/` contains the five evidence modules, the 88-module order,
  exact screen population and source hashes, runtime compatibility source,
  observed wrapper/environment, and mechanical audit scripts.
- To replay, use the repository's pinned toolchain and dependencies, apply
  the patch at the recorded base, and run the full order through
  `scripts/lean_check_tree.sh` in a fresh `TCSLIB_OLEANS` directory. Copy the
  five evidence modules into temporary `Verification/` paths and check each
  through that same script and olean tree. All five must pass. The statement
  probe is unchanged. No build command is needed.
- `SHA256SUMS` covers every other archive member. From the extracted root,
  run `sha256sum -c SHA256SUMS`. The zip's CRCs and every recorded member hash
  were also checked after archive creation.
