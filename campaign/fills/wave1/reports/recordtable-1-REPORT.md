# W1 RecordTable fill — partial delivery

**13 of 20 targets are proved, with no admissions in their axiom closures.** The seven
existential rows remain explicitly admitted. A concrete field-list copier and its
zero-field and one-field contracts are also supplied for the continuation. No private
helper is admitted, and none of the completed targets is proved modulo an admission.
This is a ground-rule-9 partial: the proof-work budget ended at the general
field-copy composition contract. The subsequent verification and packaging are complete.

## Base, scope, and freeze

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Campaign branch checked out: `complexity/arora-barak-ch3-4`.
- Base: `1e9361b5fe2022594f5b62d6d48b629d88214794`.
- Required ancestor: `78116c5d5db075c9ce46ecec0b56735d1c600bef`; the required
  `git merge-base --is-ancestor … HEAD` returned exit 0 before proof work.
- Working branch: `fill/w1-recordtable`; no rebasing, push, or PR.
- Delivery commit: `bde2e9c19ab5003bdbf215942fbe41d26615a840` (one local commit).
- Only tracked file changed: `TCSlib/Complexity/TuringMachine/Build/RecordTable.lean`.
- All 28 pre-existing public declarations, their order, and their comment-stripped
  signatures are unchanged. No public declaration was added or removed.
- The three TCSlib imports are unchanged. The one flagged added import is
  `Mathlib.Data.Nat.Bitwise`, needed for `Nat.testBit_eq_inth` in target 8.
- Final file size: **1,237 lines; 28 public / 9 private declarations**. File size is
  reported rather than used as a reason to split, as the brief's note 46 requires.

The commits between the required ancestor and the chosen base change only campaign
records/briefs, not the screen population or the verification closure's Lean sources.
The actual baseline bootstrap reported the advertised 28 sorry warnings by declaration;
there is no parallel-fill difference to subtract.

## Target status

| # | Target (`Turing.` prefix) | Status |
|---|---|---|
| 1 | `joinFields_length` | Proved |
| 2 | `fieldOffset_length` | Proved by the required public alias |
| 3 | `joinFields_cfgRecord_length` | Proved |
| 4 | `cfgRecord_field_ne_nil` | Proved |
| 5 | `cfgRecord_init` | Proved |
| 6 | `recordValid_iff_exists_cfg` | Proved, in both directions |
| 7 | `joinFields_recordTemplate_length` | Proved |
| 8 | `binDigits_posWidth_succ` | Proved |
| 9 | `TableWF.field_ne_nil` | Proved |
| 10 | `tableOffset_eq` | Proved |
| 11 | `tableOffset_length` | Proved |
| 12 | `TableAt.recordAt_take` | Proved |
| 13 | `tableRewindTM_run_ofCfg` | Proved: exact finish, first-return cut, all head bounds |
| 14 | `exists_fieldsCopyTM` | Admitted; machine and zero/one-field contracts proved |
| 15 | `exists_tableFindTM` | Admitted; original proof sketch retained |
| 16 | `exists_tableAppendTM` | Admitted; original proof sketch retained |
| 17 | `exists_recordTemplateTM` | Admitted; original proof sketch retained |
| 18 | `exists_recordInitTM` | Admitted; original proof sketch retained |
| 19 | `exists_recordValidTM` | Admitted; original proof sketch retained |
| 20 | `exists_recordNextTM` | Admitted; original proof sketch retained |

The landed corollary `RecordValid.joinFields_length` is also now admission-free, without
any edit to its proof. The seven remaining public declarations are exactly the seven
remaining direct `sorry`s in this file. Their existing docstrings each retain a literal
“Proof sketch”. **Private helpers remaining `sorry`: none. Proved-modulo targets: none.**

R8.5c `exists_inputLengthTM` remains the brief's only permitted proved-modulo dependency
for later work. This partial does not claim to have filled any of the four record-machine
rows modulo it. It does not cite `exists_recordStepTM` or any downstream complexity result.

## New private declarations

| Declaration | Role |
|---|---|
| `rt_field_cover` | Locates each cell, including the delimiters, in some field's framed interval. Minimality plus public offset lemmas; no layout induction. |
| `rt_fields_slice` | Restricts a layout to a nonempty contiguous block and proves its span is contained in the full layout. Uses `rt_field_cover` and `fieldsTape_field`. |
| `rt_copyState` | Recursive finite sum of catalog state types for a fixed number of fields. |
| `rt_copyState_fintype` | Finiteness dictionary for that state family. |
| `rt_copyState_decidableEq` | Computable equality dictionary for that state family. |
| `rt_copyEntry` | Copier's entry anchor for each field count. |
| `rt_copyExit` | Copier's exit anchor for each field count. |
| `rt_copyMachine` | Actual copier: zero-field no-op, one-field `copyTM`, and the recursive six-phase R2 composition. |
| `rt_copy_run_base` | Full target-shaped time, cut, space, and exact-finish contract for field counts at most one. |

All nine have checked axiom closures contained in `propext`, `Classical.choice`, and
`Quot.sound`. The two layout helpers are requested shared-lemma promotion candidates:
`rt_field_cover` supplies field-coordinate coverage; `rt_fields_slice` supplies the
contiguous-block frame restriction not exported by the current one-field interface.
They are private here under exclusive ownership. No escalation of a frozen statement
or an infrastructure contract is requested.

## Flagged documentation changes

- Status paragraph: 13 proved targets, seven admitted rows, field-copy frontier.
- Main-results tags: layout/record facts, table facts, and adapter changed to “proved”.
- Target 1 “Fill appendix”: reuses `length_joinFields_add_one`; only the elementary
  sum-of-lengths identity receives an induction.
- Target 13 “Fill appendix”: names the public seam visited-set theorem and prefix frame.
- Target 14 “Fill appendix (partial)”: identifies the actual recursive machine and
  the proved zero/one-field cases, without claiming the general contract.
- Target 16 “Fill appendix”: records that empty appended fields need not preserve
  `TableWF`; later seeks require nonempty appended fields (notes 25 and round-2 15).

All original sketches and attribution text are retained.

## Continuation frontier

Resume with target 14, using `rt_copyMachine`; do not build another host.

1. Prove its contract for `m + 2` fields assuming the nonempty-tail contract for
   `m + 1`. The base cases are `rt_copy_run_base`.
2. Write the source fields as `u :: tail`, with `tail` nonempty. Use
   `joinFields_cons_cons`, `fieldsTape_field`, and `rt_fields_slice [u] tail []`
   for the first-field and tail frames. The first copy leaves the separator and
   the future tail slot blank on the destination.
3. Apply, in order, `copyTM_run_ofCfg`, `skipTM_run_ofCfg` on tape 0,
   `skipTM_run_ofCfg` on tape 1, the induction hypothesis on the tail,
   and `skipBackTM_run_ofCfg` once on each tape. Compose the six runs and the
   five stationary dispatches using the public R2 theorems. Intercept every exit.
4. The intended exact composition time is the tail time plus `6 * u.length + 17`.
   Since the layout length is `u.length + 1 + tail-layout-length`, increasing
   the tail's linear constant by 20 suffices for the time and head-radius
   inequalities. Formalize the two destination write masks as the single final
   layout write, and discharge the cuts and visited-set containment. These are
   the outstanding obligations; no theorem currently asserts them without `sorry`.
5. Package the state type, its two instances, the machine, and its anchors to fill
   `exists_fieldsCopyTM`. Then proceed to find, append, and the four record rows
   in the brief's order. For find, retain the escape before the final accepted
   field's skip and use `counterLoopTMVia`; for template, use R8.5c and the
   increment-plus-overflow-extension route.

The frozen `cfgRecord` definition elaborates its window indices through a list
coercion from naturals to integers. The completed layout proofs normalize that
coercion with `Bind.bind`, `Pure.pure`, and `← List.map_eq_flatMap`; do not change
the definition to avoid this elaboration detail.

The two-field execution probes are only sanity checks of the concrete copier,
not proofs of the missing general contract. The empty-tag probe establishes that
there are no valid records with tag type `Empty`, executes the empty enumeration's
first-lookup/no branch, and checks a concrete zero-time no controller. It does not
claim that the general admitted `exists_recordNextTM` implementation is executable.

## Verification and duplication

The baseline bootstrap checked all 55 modules with zero errors and 28 sorry
warnings, matching `logs/base-sorries.txt` by declaration. It is included in
`logs/bootstrap.log`. The full after-screen also passed, as recorded below.

The eight unchanged out-of-scope admissions are:

| Module | Declaration(s) |
|---|---|
| `Build/CfgRecord` | `exists_recordStepTM` |
| `NDCodes` | `exists_effectiveNDMachineCode` |
| `Build/InputLength` | `exists_inputLengthTM` |
| `Build/CertShell` | `FinTM.exists_certificateShell` |
| `Build/OracleSim` | `FinOracleTM.exists_plain_simulation`, `FinOracleNDTM.exists_choiceTM` |
| `CodeSimulator` | `exists_polyCanonizer`, `exists_uniformSimulator` |

`logs/freeze-check.log` records the public-signature/order comparison, unchanged
TCSlib imports, all private names, and the exact seven remaining public sorries.
`git diff --check` passed. `logs/scope.log` records the one changed tracked path.
`logs/style-lint.log` ends with:

```text
style_lint: 0 FAIL, 8 WARN over 20 files
```

The warnings include the owned file's 1,237-line size. Note 46 explicitly permits
this; there are no style failures. The original two §12.8b sanity cases are
preserved byte-for-byte in `verification/S128bStatementsProbe.lean`.

The single patch applies to a temporary index at the recorded base, and its
resulting tree is identical to the delivery commit's tree (see
`logs/patch-check.log`). The incremental bundle verifies and names the recorded
base as its prerequisite (`logs/bundle-verify.log`).

### Final Lean verification

The fresh final sweep completed with **exit 0, 55/55 modules, zero errors, and
exactly 15 sorry warnings**: the seven remaining owned targets plus the eight
unchanged out-of-scope declarations listed above. The names were resolved from
the warning locations and compared against the baseline (`logs/final-sorry-names.txt`
and `logs/verification-audit.log`). The owned module has no other warnings.

`logs/axiom-print.log` prints all 20 targets and the landed corollary. The 13
completed targets and `RecordValid.joinFields_length` have axiom closures contained
in `[propext, Classical.choice, Quot.sound]`. Only the seven reported unfinished
rows contain `sorryAx`. `logs/private-axioms.log` checks every new private declaration;
none contains `sorryAx` or any nonstandard axiom.

All five evidence modules passed against the fresh final olean tree, each with
exit 0 and zero errors/warnings:

| Evidence | Log | Result |
|---|---|---|
| Every target and the landed corollary | `logs/axiom-print.log` | Expected closures |
| All nine private helpers | `logs/private-axioms.log` | Admission-free |
| Original last-match and empty-field append cases | `logs/preship-probe.log` | Passed, probe unchanged |
| Empty-`T` enumeration/no branch (note 50) | `logs/empty-tag-probe.log` | Passed, executed `rfl`/`decide` examples |
| Two-field copier, including empty fields and nearby nonblank frame cells | `logs/fields-copy-probe.log` | Passed, executed `decide` examples |

Final sweep tail:

```text
TCSlib/Complexity/TuringMachine/Build/RecordTable.lean:1126:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/RecordTable.lean:1187:8: warning: declaration uses 'sorry'
CHECK TCSlib/Complexity/TuringMachine/Build/CertShell
TCSlib/Complexity/TuringMachine/Build/CertShell.lean:71:8: warning: declaration uses 'sorry'
CHECK TCSlib/Complexity/TuringMachine/Build/OracleSim
TCSlib/Complexity/TuringMachine/Build/OracleSim.lean:212:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/OracleSim.lean:398:8: warning: declaration uses 'sorry'
CHECK TCSlib/Complexity/TuringMachine/CodeSimulator
TCSlib/Complexity/TuringMachine/CodeSimulator.lean:205:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/CodeSimulator.lean:239:8: warning: declaration uses 'sorry'
CHECK TCSlib/Complexity/TuringMachine/Robustness/Bidirectional
CHECK TCSlib/Complexity/TuringMachine
```

Every Lean invocation used `scripts/lean_check_tree.sh`; no `lake build` was run.
The pinned mathlib package cache was reused after comparing `lake-manifest.json`
byte-for-byte. Development checks used matching-source cached upstream oleans;
the baseline bootstrap and final 55-module sweeps use fresh, separate olean trees.

Lean 4.25's startup looks up `/proc/<its-own-pid>/exe`, which is unavailable in
this execution environment while `/proc/self/exe` is available. The supplied
`verification/lean-self-exe.c` redirects only that exact self lookup to its
self alias. No Lean binary, kernel, check script, or repository infrastructure was
modified. The check scripts otherwise ran unchanged. The compatibility source is
included for transparency; ordinary environments need no such wrapper.


### Duplication review

The exact 24-file population from the brief is recorded in
`verification/screen-population.txt`. Both runs use the unchanged original
`audits/evidence/retrofit/copy-text-screen.py`. The full before output is
`logs/screen-before.txt` and is byte-identical to the issue-tree baseline.

Exact before header (full output in `logs/screen-before.txt`):

```text
declarations screened: 1331; copy pairs (target reproduces >= half of source): 1717; reproduced text: 574,720 chars
```

Exact after header (full output in `logs/screen-after.txt`):

```text
declarations screened: 1350; copy pairs (target reproduces >= half of source): 1724; reproduced text: 575,319 chars
```

There are seven added pairs, zero removed pairs, and **zero new cross-file pairs**
involving the owned file. The total measured-text increase is 599 characters.
The complete before/after outputs and the set difference are shipped, not merely
these headline counts. All seven new pairs are listed and justified below;
`RecordTable.lean::` is omitted from both name columns.

| Target reproduces | Source | Match | Justification |
|---|---|---|---|
| `rt_copyState_fintype` | `rt_copyState` | 76/104 = 73% | The finiteness dictionary repeats the recursive sum type whose instances it constructs. |
| `rt_copyState_decidableEq` | `rt_copyState` | 76/104 = 73% | The equality dictionary repeats that same state type to select its computable instances. |
| `rt_copyState_decidableEq` | `rt_copyState_fintype` | 92/130 = 71% | Distinct typeclass dictionaries follow the same zero/singleton/successor cases. |
| `rt_copyState_fintype` | `rt_copyState_decidableEq` | 92/138 = 67% | Reverse direction of the shared structural recursion; the produced dictionaries differ. |
| `rt_copyState` | `rt_copyState_fintype` | 76/130 = 58% | The state-family expression is repeated in its finiteness type ascription. |
| `joinFields_cfgRecord_length` | `cfgRecord_init` | 111/198 = 56% | Both normalize the frozen codec's list coercions; their length and initial-value conclusions are different. |
| `rt_copyState` | `rt_copyState_decidableEq` | 76/138 = 55% | The state-family expression is repeated in its decidable-equality type ascription. |

Every new pair is below the brief's 90% copy threshold. The added proofs cite the
public catalog, seam, and layout contracts; no private proof from another file was
copied. **new copies: none.** The owned file's copied-proof ledger has no new copied
material. No pre-disclosed exception or duplication escalation is used.

## Applying or reviewing the delivery

- `TCSlib/Complexity/TuringMachine/Build/RecordTable.lean` is the complete modified source.
- `patches/0001-Prove-record-table-layout-facts-and-rewind-adapter.patch` is the
  one-commit `git format-patch` series against the recorded base. Integration may
  use `git am -3` as the campaign workflow prescribes.
- `fill-w1-recordtable.bundle` contains the same commit and branch, with the base
  commit as its prerequisite. No push or PR was performed.
- `verification/` contains the five Lean evidence files, the freeze checker, the
  check order, the exact screen population, and the environment compatibility source.
  The evidence files are not repository changes. To rerun them, place them in a
  temporary `Verification/` directory at the repository root and invoke
  `bash scripts/lean_check_tree.sh Verification/<name>` for each, after the ordered
  module sweep with the same `TCSLIB_OLEANS` setting.
- `logs/` contains complete verification outputs. `SHA256SUMS` covers every other
  archive member and can be checked from the extracted archive root with
  `sha256sum -c SHA256SUMS`.
