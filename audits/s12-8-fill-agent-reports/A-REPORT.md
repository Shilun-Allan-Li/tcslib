# §12.8 stream A — complete fill

Complete: **13/13 targets proved**, with no `sorry` in either owned source and no `sorryAx` in any of the fifteen required axiom prints. The proved-modulo set is empty. No escalation or requested shared lemma. No push, PR, rebase, or new tracked file.

## Base and ownership

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Checked out `complexity/arora-barak-ch3-4`, then created `fill/s128-A`.
- Work base: `37ab609199b2fad253b136375243db20faf88b16`.
- Local delivery commit: `5aa646d6bb9abd990492c827ef262bad9594436c` (Codex <codex@openai.com>).
- Before proof work, `git merge-base --is-ancestor 182e6f44c5135f07cb4965a42fc6865da720d553 HEAD` passed (exit 0). Rechecked against the recorded base.
- The owned sources, all 99 prescribed bootstrap Lean sources, the checker, and all three probe sources are byte-identical between the required issue commit and this base. The supplied attachment equals the branch's `briefs/s128-fill-A.md`.
- Only `TCSlib/Complexity/TuringMachine/Build/Catalog.lean` and `TCSlib/Complexity/TuringMachine/Build/Seam.lean` changed. All experiments, logs, and delivery files stayed outside the tracked source tree (temporary Lean probes were in ignored `.lake`).
- Imports and attribution text are unchanged. No new public declaration/export, no removed declaration, and no change to any other landed definition or proof body.

The archive contains the full two sources, a local commit's format-patch series and incremental git bundle against the base, this report, the final sweep/axiom logs, supporting evidence, and `SHA256SUMS`. The bundle requires the base commit. Integration remains the maintainer's G1 PR process.

## Completed targets and shared arguments

| # | Target | Proof route |
|---|---|---|
| 1 | `fieldsTape_field` | Induction on the field index; cites `fieldsTape_cons_shift`, `fieldOffset_cons_succ`, and `joinFields_cons_cons`. |
| 2 | `scanResult_fold` | `scanResult_keep`, then one structural Mealy induction with the fold invariant. |
| 3 | `scanResult_map` | `scanResult_keep`, then one structural Mealy induction with the map invariant. |
| 4 | `scanResult_shiftRight` | `scanResult_keep`, then one list induction, generalizing the boundary value. |
| 5 | `scanResult_shiftLeft` | Cites target 4 on `w.reverse`, `mealyRun_keep`, and the single `shiftLeft_list` identity; no new induction. |
| 6 | `scanResult_carry` | `scanResult_keep`, one list induction, and the carry-clear fact. |
| 7 | `scanTM_run_ofCfg` | One `catalog_trace_run` instance covering both passes; forward writes cite `catalog_write_take`, return writes cite `catalog_write_middle`. |
| 8 | `compareTM_run_ofCfg` | Cites the existing compare trace generalized in place; no second compare trace. |
| 9 | `skipTM_run_ofCfg` | The shared one-pass corollary, with a forward read-only frame. |
| 10 | `skipBackTM_run_ofCfg` | The same corollary, with the unconditional first two moves and the left-delimiter return. |
| 11 | `seekEndTM_run_ofCfg` | The same corollary, the sole no-double-blank layout fact, and the public end-offset/length identity. |
| 12 | `seekStartTM_run_ofCfg` | The same corollary and layout fact; uses `hcur` and target 1 at the two boundary cases, including the empty table. |
| 13 | `seamCompTM₂_run_ofCfg` | Both branches cite `seamCompTM_runFrom_left` and `seamCompTM_run_ofCfg` for right lockstep; no new induction. |

Every scan write/move and seek move cites the public action-step layer, directly or through `catalog_seek_step`, which is only a specialization to the shared seek frame. Scan and seek exit stationarity cite `step_of_inputMoveAction` at zero. The compare table retains its existing literal-action proof route, as expressly required by route 4. No public shared lemma was privately re-proved.

### New private declarations (12, all in Catalog Part 3)

| Declaration | Role |
|---|---|
| `catalog_pass_contract` | H-pass: specializes `catalog_trace_run` to a stationary return family and extracts finish, cut, and trajectory; shared by all four seeks, with no time induction. |
| `catalogSeekCfg` | Shared read-only seek frame with one relative head displacement and control state. |
| `catalog_seek_step` | Specializes `step_of_tapeAction_move` to that frame; only configuration-update normalization follows the citation. |
| `fieldsTape_no_double_blank` | H-lay: the sole new layout fact, proved through the public shifted-tail layout and target 1. |
| `mealyRun_append` | H-scan: split a Mealy run at an append. |
| `mealyRun_induction` | Shared structural Mealy induction, factoring the repeated induction skeleton of keep/length/fold/map after the initial text screen found two pairs over 90%. Each invariant is a separate instance of this one induction rule. |
| `mealyRun_length` | H-scan: every transducer step emits one cell. |
| `mealyRun_next` | Identify the next prefix state and corresponding full-output cell from `mealyRun_append`; used by the scan's forward step. |
| `mealyRun_keep` | H-scan: the identity transducer preserves the state and word. |
| `scanResult_keep` | H-scan: reduce an identity return pass to the forward Mealy run. |
| `shiftLeft_list` | The single reversed-zip identity used to derive left shift from right shift. |
| `mealyRun_carry_clear` | A cleared carry preserves the remaining word and flag. |

There are no new declarations in Seam. The scan's `F`, `R`, and finish `D`, and each seek's `F` and finish `D`, are local families inside their proof bodies. The scan forward family uses the brief's authorized written-prefix-over-the-original-tape alternative. Its return family uses the forward output prefix and reversed backward output; the only run induction is the cited public trace. The seeks use the prescribed lengths `|w|`, `|u|+2`, `D`, and `D+3` in H-pass.

## Explicitly flagged authorized changes

### Two public body swaps

1. **`compareTM_run`**: new body cites the generalized `catalog_compare_trace` at `d := Cfg.ofWords .run w`. Statement byte-identical.
2. **`compareTM_spaceUsedByTape`**: new body cites the same specialization, then the existing `catalog_space_bound` and `catalog_space_one`. Statement byte-identical.

Both retain the aliased `fst = snd` case: the private trace requires no distinctness hypothesis. Neither canonical row attempts to derive from the public framed row, whose frozen statement has `hne`.

### Four private in-place generalizations

1. **`catalog_compare_stop`**: only its types generalized to an alphabet with decidable equality; proof body verbatim. Docstring changes “bits” to “symbols”.
2. **`catalogCompareF`**: replaces the canonical frame by arbitrary `d`, preserving all other fields and advancing each selected physical head once. Docstring synchronized.
3. **`catalogCompareR`**: replaces the canonical return frame by arbitrary `d`, with verdict and relative return displacement. Docstring synchronized.
4. **`catalog_compare_trace`**: replaces the canonical trace in place by the alphabet-generic framed trace with `hu`, `hv`, `hstate`, and no `hne`. One public `catalog_trace_run` instance remains. Docstring synchronized.

These are replacements: the compare private declaration count is unchanged, and the old canonical families/trace do not survive beside them.

**D2, frozen `hne`:** `compareTM_run_ofCfg` consumes it with `have _ := hne`, with a comment explaining that the shared trace covers aliasing. No hypothesis is removed or weakened.

**D3, one-sentence docstring corrections:**

- `compareTM_run_ofCfg`: the canonical and framed rows derive from the same framed trace, correcting the former sentence saying the canonical row derives from the public framed form.
- `scanResult_map`: the proof sketch now says to generalize the accumulator and apply the shared Mealy induction, matching the factored proof. The mathematical invariant and conclusion are unchanged.

**Status updates (each authorized by the brief):** Catalog's module Status paragraph; both “Part 3 … (statement layer)” labels, now “(proved)”; Part 3's section-docstring pending/sorried sentence; the Main results “Part 3 (statements)” label; and Seam's “proved, except the §12.8 row” paragraph. No other status/attribution edits. No sketch appendices.

## Frozen surface and sizes

`evidence/statement-freeze.log` verifies the raw statements of all thirteen targets and both swapped public rows byte-for-byte. A comment-stripped comparison verifies that every other landed declaration/body is unchanged except the four explicitly authorized private replacements. The `catalog_compare_stop` proof body also matches verbatim. `git diff --check` passes.

| File | Base lines | Final lines | Final bytes | Declaration count |
|---|---:|---:|---:|---|
| `Build/Catalog.lean` | 11,970 | 12,732 | 652,135 | 468 → 480; 89 public, 391 private |
| `Build/Seam.lean` | 815 | 854 | 47,347 | 30 → 30; 18 public, 12 private |

Catalog's size split remains the acknowledged 12.2c work; this batch does not introduce a new module.

## Verification

Only `scripts/lean_check_tree.sh` was used for Lean checks. `lake build` was never run. Lean is the pinned v4.25.0, and the pinned Mathlib cache was obtained through `lake exe cache get` (including the targeted `Mathlib.Logic.Equiv.Bool` cache retry).

The managed runtime could not resolve its `/proc/<pid>/exe` path. A per-command `LD_PRELOAD` shim redirects only that exact readlink to `/proc/self/exe`; it does not change Lean code, axioms, imports, or the checker. Its source is included as `evidence/lean-self-path.c` for reproducibility. After stopping an unfinished bulk cache operation, the baseline bootstrap was resumed following two transient SIGBUS failures at an unchanged upstream module and a missing cached Mathlib olean. All 99 prescribed modules then passed; the baseline/resume logs retain these events rather than hiding them.

All three pre-ship probes were rerun on the baseline, which is byte-identical to the issue commit for their entire Lean/checker population. The ordinary and visibility probes gave zero errors and warnings. The lint-behavior probe gave the expected two unused-variable warnings, one sorry warning, and two structure-layout syntax errors documented in its header. It is intentionally negative, not a final validation failure.

The final checks are complete:

| Check | Result |
|---|---|
| Prescribed bootstrap | All 99 modules passed; base sorry-warning set exactly 41. |
| Owned sources | Both pass; 0 errors, 0 sorry warnings. Catalog's non-sorry warning count falls from 100 to 90; Seam remains 5. No new warning. |
| Fifteen downstream modules | All pass; 0 errors, exactly the same 19 sorry warnings and no new non-sorry warnings. |
| Final pre-ship and visibility probes | Both pass; 0 errors, 0 warnings. |
| Fifteen axiom prints | Only `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx`. |
| Campaign style lint | `style_lint: 0 FAIL, 6 WARN over 16 files`; the six file-size warnings are pre-existing categories. |
| Surface/ownership | All fifteen raw statements byte-identical; only the two owned source files changed; clean worktree. |
| Packaging | Patch replay reconstructs the committed tree exactly; incremental bundle verifies. |

The downstream sorry counts remain: `CfgRecord` 5, `TQBF` 4, `Scan` 4, `InputCall` 2, `Zone` 2, `CounterLoop` 1, and `Codes2Tape` 1. All other eight downstream modules are sorry-free. The nine baseline upstream sorries are untouched and are not dependencies of the proved stream-A targets.

During the final factoring pass, an earlier downstream attempt reached `Build/Scan` while Catalog's scratch olean was being regenerated and stopped because that object was temporarily absent (`evidence/downstream-iteration1.log`). After Catalog passed, all fifteen downstream modules were rerun from the start. The delivered `final-sweep.log` combines the two successful final owned checks with that successful complete downstream sweep; it contains no error or failure.

Final sweep tail:

```text
TCSlib/Complexity/ClassPSPACE/TQBF.lean:282:8: warning: declaration uses 'sorry'
PASS TCSlib/Complexity/ClassPSPACE/TQBF
CHECK TCSlib/Complexity/ClassPSPACE
PASS TCSlib/Complexity/ClassPSPACE
CHECK TCSlib/Complexity/CookLevin
PASS TCSlib/Complexity/CookLevin
CHECK TCSlib/Complexity/TuringMachine
PASS TCSlib/Complexity/TuringMachine
CHECK TCSlib/Complexity/TuringMachine/Build/Zone
TCSlib/Complexity/TuringMachine/Build/Zone.lean:1109:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Zone.lean:1145:8: warning: declaration uses 'sorry'
PASS TCSlib/Complexity/TuringMachine/Build/Zone
CHECK TCSlib/Complexity/TuringMachine/Codes2Tape
TCSlib/Complexity/TuringMachine/Codes2Tape.lean:547:8: warning: declaration uses 'sorry'
PASS TCSlib/Complexity/TuringMachine/Codes2Tape
FINAL: 17/17 modules PASS; 0 errors; owned sorry warnings 0; downstream sorry warnings 19 (base unchanged).
```

The fifteen axiom prints (also in `axioms.log`):

```text
'Turing.fieldsTape_field' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.scanResult_fold' depends on axioms: [propext]
'Turing.scanResult_map' depends on axioms: [propext]
'Turing.scanResult_shiftRight' depends on axioms: [propext]
'Turing.scanResult_shiftLeft' depends on axioms: [propext]
'Turing.scanResult_carry' depends on axioms: [propext]
'Turing.scanTM_run_ofCfg' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.compareTM_run_ofCfg' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.skipTM_run_ofCfg' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.skipBackTM_run_ofCfg' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.seekEndTM_run_ofCfg' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.seekStartTM_run_ofCfg' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.seamCompTM₂_run_ofCfg' depends on axioms: [propext, Quot.sound]
'Turing.compareTM_run' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.compareTM_spaceUsedByTape' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Duplication review

**New copies: none.** There is one generalized compare trace (no surviving canonical duplicate), one scan instance of the public trace, and one H-pass shared by the four seeks. Seam reuses both public sequencing lemmas and has no new induction or helper. No new cross-file pair involves an owned declaration in either population, and the extended screen adds no new/changed pair involving `Sweep` or `StateRenaming`.

The initial fill screen caught `mealyRun_keep → mealyRun_length` at 95% and `scanResult_fold → scanResult_map` at 91%. These were factored into the shared `mealyRun_induction`, used by all four consumers. The final screens below are after that factoring. There is no final new or changed pair at 90% or more, including outside hazard (2).

The full outputs are included in `evidence/screen-before.txt`, `screen-after.txt`, `screen-extended-before.txt`, and `screen-extended-after.txt`. Their headline outputs, verbatim:

Round-2 population, before:

```text
declarations screened: 550; copy pairs (target reproduces >= half of source): 415; reproduced text: 121,938 chars
```

Round-2 population, after:

```text
declarations screened: 576; copy pairs (target reproduces >= half of source): 422; reproduced text: 125,204 chars
```

Extended watch population, before:

```text
declarations screened: 568; copy pairs (target reproduces >= half of source): 421; reproduced text: 123,669 chars
```

Extended watch population, after:

```text
declarations screened: 594; copy pairs (target reproduces >= half of source): 428; reproduced text: 126,935 chars
```

Both populations have the same **8 new, 4 changed, and 1 removed directed pair**; net +7 pairs and +3,266 reproduced characters. These are the complete new/changed in-file pairs, all in Catalog. An arrow means “target reproduces source” in the screen's tiling metric; it is not a dependency arrow.

| Kind | Directed pair | Before → after | One-line justification |
|---|---|---|---|
| New | `catalogIncR → catalogCompareR` | — → 63/91 (69%) | Both use a framed return displacement; comparison preserves tapes and carries a verdict, while the increment return describes its distinct rewritten word/control. No trace or proof is duplicated. |
| New | `skipBackTM_run_ofCfg → skipTM_run_ofCfg` | — → 969/1430 (68%) | Both instantiate H-pass and specialize the shared seek frame; the backward phase sequence and delimiter return differ, with no copied time induction. |
| New | `scanResult_fold → scanResult_map` | — → 92/138 (67%) | Both are short instances of the factored Mealy induction, with distinct accumulator/output invariants. |
| New | `scanResult_map → scanResult_fold` | — → 92/145 (63%) | Reverse direction of the same two shared-induction instantiations; the induction itself occurs once. |
| New | `seekEndTM_run_ofCfg → skipTM_run_ofCfg` | — → 859/1430 (60%) | Common H-pass/trajectory setup; the end seek's blank-pair control and H-lay obligations are distinct. |
| New | `seekStartTM_run_ofCfg → skipTM_run_ofCfg` | — → 825/1430 (58%) | Common H-pass/trajectory setup; the start seek has a leftward phase sequence and two-cell return, not a second run induction. |
| New, D4 | `compareTM_spaceUsedByTape → transferTM_spaceUsedByTape` | — → 322/627 (51%) | Authorized canonical space specialization, inside the acknowledged R3 sibling family; cites the existing space helpers. |
| New, D4 | `compareTM_run_ofCfg → compareTM_run` | — → 193/384 (50%) | The framed and canonical consequences share the generalized compare trace, inside the acknowledged R3 sibling family. |
| Changed, D4 | `compareTM_spaceUsedByTape → compareTM_run` | 237/318 (75%) → 286/384 (74%) | Both authorized bodies specialize the same generalized trace at `Cfg.ofWords`; no extra trace. |
| Changed, D4 | `compareTM_spaceUsedByTape → copyTM_spaceUsedByTape` | 315/581 (54%) → 322/581 (55%) | Existing acknowledged R3 space-wrapper similarity; the swap cites `catalog_space_bound`/`catalog_space_one`. |
| Changed, D4 | `transferTM_spaceUsedByTape → compareTM_spaceUsedByTape` | 311/573 (54%) → 322/637 (51%) | Reverse coverage against the authorized canonical-space replacement, inside the same acknowledged family. |
| Changed, D4 | `copyTM_spaceUsedByTape → compareTM_spaceUsedByTape` | 315/573 (55%) → 322/637 (51%) | Reverse coverage against the authorized canonical-space replacement, inside the same acknowledged family. |

Removed: `compareTM_spaceUsedByTape → clearTM_spaceUsedByTape`, formerly 223/434 (51%). No framed-compare/transfer/copy/clear closing pair was newly flagged; all hazard-(2) pairs actually changed or added are named above. They are retained under the brief's D4 instruction, rather than factored in this batch. The other unchanged historical pairs retain their existing acknowledgments.

### Cumulative copied-material accounting

The ledger's historical Catalog figure is **318/459 = 69.3%** (strict: 283/459 = 61.7%), with its existing 12.2c acknowledgment. At this pre-issue work base the declaration denominator is 468; after the 12 new private helpers it is 480. The acknowledged member counts do not grow: **Catalog 318/480 = 66.3%**, strict **283/480 = 59.0%**. The six compare replacements do not change declaration counts. Same-file similarities above are handled by the inherited in-file convention and D4, not newly copied members. **Seam remains 0/30 = 0%**. No mandatory new-copy backlog item is triggered; the existing cleanup and size acknowledgments remain in force. A text-screen result is not used as a substitute for the semantic sharing review above.

## Reproduction and delivery integrity

Use the recorded base and apply the patch with `git am -3 patches/*.patch`, preserving the local agent commit's authorship, or import the incremental bundle's `fill/s128-A` ref into a repository containing the base. `evidence/patch-verify.log` records that applying the series in an isolated index produces exactly the committed tree; `evidence/bundle-verify.log` records the bundle's base prerequisite and successful verification.

Obtain the pinned dependency cache with `lake exe cache get`. Bootstrap the order in `briefs/orders/s128-fill-A.txt` by calling `bash scripts/lean_check_tree.sh "$m"` on each module in order, stopping at any nonzero exit. Final owned/downstream checks use the same script; the fifteen downstream paths, in dependency order, are in `evidence/downstream-order.txt`. The existing probe sources are under `audits/evidence/s12-8/`; copy them into ignored `.lake` with `.lean` extensions and check them with the script. `evidence/S128FillAAxioms.lean.txt` is the source for the fifteen axiom prints. The intentionally negative lint probe is only a baseline behavior check.

In the managed runtime used here, the readlink compatibility shim can be compiled with `cc -shared -fPIC evidence/lean-self-path.c -ldl -o <scratch>/lean-self-path.so` and supplied via `LD_PRELOAD` to the checker invocation. An ordinary Lean installation does not need this environment-only workaround. No changes to repository scripts were made.

Reproduce the primary copy-text screen with the exact population in the brief: `Build/{Catalog,Seam,CounterLoop,Embed}`, `TuringMachine/{Simulation,SymbolLift}`, `ClassPSPACE/TQBF`, and `Build/{Scan,InputCall,CfgRecord}`; the extended run adds `TuringMachine/{Sweep,StateRenaming}`. Full file paths, commands, and the shared before/after pair delta are in `evidence/screen-commands.txt`, the four screen logs, and `evidence/screen-diff.txt`.

`SHA256SUMS` covers every archive member other than itself. Sources in the archive equal the committed files. The archive does not include build artifacts or dependency caches. No PR was opened and nothing was pushed.
