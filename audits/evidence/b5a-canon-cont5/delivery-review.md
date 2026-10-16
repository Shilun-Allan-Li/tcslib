# Review — B5a canonizer continuation 5 (`MachineFormat.exists_polyCanonizer`), delivery `fill-b5a-canon-cont5.zip`

**Verdict: READY TO INTEGRATE, as an escalation partial.** E1 is ruled (user, 2026-10-16): the
`phaseHostTM` adapter with a fresh anchor is authorized for cont6. The delivery:
- applies the prescribed factoring patch unchanged as its first commit (verified byte for
  byte);
- proves `exists_canonDecider` modulo the still-open frozen stub `exists_canonGrammarStage`;
- adds the two permitted leaves (the native all-`true` suffix scan, the one-step emitting
  halt) and a three-port emit adapter over the public `phaseHostTM`;
- leaves the headline's admission walk naming only `exists_canonGrammarStage`.

There is no new admission, public declaration, import, unowned edit or copy pair, and every
check passes at the current tip. E1 is genuine: the brief's pitfall that C2 can be the
counter-loop body "without a wrapper" is false. `counterLoopTM_run_done` and
`counterLoopTM_run_escape` need each round to start at the anchor `a` and return to that same
`a`. C2's contract starts at `entry` and stops at a distinct, stationary `exit true`, with no
return-to-entry clause (I verified the worker's diagnostics in-module). The requested
`phaseHostTM` adapter, with a fresh anchor, is now authorized for cont6 (user, 2026-10-16). The
partial lands once its screens come back clean.

Review conditions:
- Campaign tip at review: `67c2c56cdfcd6ed550f2fd9cca1338953ff9583e`, later
  `8b383e0bfcf69c1a036cba366caf7ae434e59429`. Both have Lean content `e5fcd8ee`; no `.lean`
  file differs.
- The tip is now `c2897d7f` (#110, #111). Those PRs changed only `UniversalStartup` and
  `WindowClock`. Neither is in `CodeSimulator`'s upstream closure (29 TCSlib modules), and
  `CodeSimulator` itself is unchanged. graph2 at `c2897d7f` gives the same 9-module replay list.
  So everything below holds at `c2897d7f`, elaborated against `oleans-lwalk`.
- Snapshot: `oleans-lwalk`.
- Worktrees: `review/cont5/wt-tip`, `review/cont5/wt-tipd` (tip plus the delivered file),
  `review/cont5/wt-base` (`596cae56`, reset after the patch checks).

## Checks

| # | Check | Result | Key output |
|---|---|---|---|
| 1 | Zip SHA-256 | PASS | `52e94a6053f9fbca458f9af78c769b63c3d06efda13b716209f308fc0cd4dba0` |
| 2 | Extraction | PASS | new empty `review/cont5/x`, 58 files, no symlinks |
| 3 | `SHA256SUMS` | PASS | 57/57 OK; covers every file except itself |
| 4 | Shim and scripts | PASS | `evidence/runtime/executable-path.c` = `985924ad…4fba7`, not compiled or run. `evidence/tools/compare-screens.py` and `freeze-check.py` were not run. No other C files |
| 5 | Brief and dispatch | PASS | tip `briefs/b5a-fill-canon-cont5.md` with `@ANCESTOR@`→`596cae56…` is byte-equal to `infra_local/fill-dispatches/b5a-fill-canon-cont5.md` (`ecf6553c…1ccac5`) |
| 6 | Base | PASS | REPORT base `596cae56ebc74f18628a2f8003ca407db90f1d2f`, an ancestor of the tip |
| 7 | Bundle | PASS | `tcslib.bundle` verifies; prerequisite `596cae56`; ref `fill/b5a-canon-cont5` = `7ba42d0f8ee1091a986c34292c7f4c5a59c1aba7`. Commits: `899d0796de24827efff274521335a01ca1f4bbab` (parent `596cae56`, factoring), then `7ba42d0f` (worker). Each changes only `CodeSimulator.lean` |
| 8 | Factoring commit == `git apply factor.patch` | PASS | the zip's `evidence/factor.patch` is byte-equal to the repository's `audits/evidence/b5a-canon-cont5/factor.patch` (`e9409c9c…30fa`). In `wt-base`, `git apply --check` and `git apply` give a `CodeSimulator.lean` byte-equal to `899d0796:CodeSimulator.lean` |
| 9 | Patch series | PASS | `0001` at the base → commit-1 file; then `0002` → the delivered file (byte-equal; SHA-256 `0944317441c90818992e0d2541e06eb86ba690a541afe435942f108161df2ac6`, as REPORT says) |
| 10 | Ownership (commit 1 → delivered, patched-tree lines) | PASS | difflib opcodes: an insert after 4435 (home, 177 lines); appendices at 4447 (grammar, +7), 4474 (validator, +6), 4591 (headline, +6), each keeping the old text; decider body 4480–4487 replaced. Unowned changes: none. Lines 1–4434 and everything from 4592 on are byte-identical: the headline statement, glue, D4 section and H1 region |
| 11 | Freeze | PASS | `declfreeze` base→delivered: `public 11 11`, none added or removed; `exists_polyCanonizer` changes in docstring only. `privstmt.py`: `STATEMENT CHANGED: []` over 149→155 declarations. Body changes: `exists_canonStripTM`, `canonPatchWord` (the patch), `exists_canonDecider`, plus docstring-only changes to `exists_canonGrammarStage` (statement and `sorry` body identical) and the headline |
| 12 | `canonPreserveInstall` | PASS | byte-identical (80 lines) at base, commit 1 and delivered (line 1241) |
| 13 | H1 and D4 regions | PASS | inside the byte-identical suffix (D4: patched 4639–4693 = delivered 5002–5056; H1 `h1HostedVerdictTM`…`exists_uniformSimulator`: patched 4694–4891 = delivered 5057–5254) |
| 14 | Hygiene (393 added lines, 373 the worker's) | PASS | none of the forbidden constructs, `sorry`, `set_option`, `open`/`section`/`variable`, attributes |
| 15 | Widths | PASS | added lines at most 95 characters. The one line over 100 in the file (1131, 102 characters) is pre-existing in the base |
| 16 | Rule 11 | PASS | no R3 row in the added lines. All external TCSlib names in the added proofs (e.g. `seamCompTM_runFrom_left`, `runFrom_mapState_of_agreeOn`, `phaseHostTM_run`, `embedEmitTM_frame`) were already cited by the base file, so there is no new external citation |
| 17 | `CodeSimulator.lean` unchanged base→tip | PASS | 0 diff lines. Lean changes `596cae56`→tip are `Build/Catalog`, `Build/Contract/Catalog` and `Build/Zone` (#108, #109); `declfreeze`: no public statement changed (publics added in Catalog: `walkTM`, `walkTM_run_ofCfg`, `skipTM_eq_walkTM`) |
| 18 | Elaboration at tip, delivered | PASS | exit 0, 0 errors; exactly 2 sorry warnings: `:4632:14` (`exists_canonGrammarStage`) and `:5245:8` (`exists_uniformSimulator`) |
| 19 | Elaboration at tip, tip's own file | baseline | 3 sorry warnings: 4443 (grammar), 4470 (decider), 4877 (uniform simulator) |
| 20 | New warnings (`warndiff.py`) | PASS | `warnings base/new: 3 2`; `new warnings: 0`; removed: `exists_canonDecider`'s sorry |
| 21 | Axiom prints (in-module) | PASS (partial) | `exists_polyCanonizer`, `exists_uniformSimulator`: `[propext, sorryAx, Classical.choice, Quot.sound]`. `canonPatchWord_le`, `canonPatchWord`: `[propext, Quot.sound]`. `exists_canonStripTM`, `canonSuffix_run`, `canonEmitVerdict`: `[propext, Classical.choice, Quot.sound]`. `canonSuffixTM`, `canonHaltTM`: no axioms. `canonHalt_run`: `[propext, Quot.sound]`. `exists_canonDecider`: `[propext, sorryAx, Classical.choice, Quot.sound]`; `exists_canonGrammarStage`: `[propext, sorryAx, Quot.sound]`. The other 9 publics carry no `sorryAx` |
| 22 | Headline admission walk (`#sorry_sources`) | PASS (partial) | delivered: `exists_polyCanonizer: [… exists_canonGrammarStage]`; tip before: `[… exists_canonDecider, … exists_canonGrammarStage]` |
| 23 | E1 diagnostics (the worker's `InternalProbeAppendix`, read; appended to the delivered module) | PASS | `cont5_record_entry_ne_true` `[propext]`; `cont5_record_true_stationary`, `cont5_record_true_run` `[propext, Quot.sound]`; 0 errors |
| 24 | Probes at tip (as is, tip olean) | PASS | `CanonCont4ImportProbe` 130/130, `CanonCont3ImportProbe` 118/118, `B5aContPreShip` 15/15: 0 errors, 0 warnings. `B5aStatementsProbe`: 0 errors, 1 sorry warning (its probe-local `exists_timedSimulator`, line 233). `S1210StatementsProbe`: 0 errors, 1 sorry warning (probe-local, line 182); control `EXP_subset_POracle_EXPCOM` still detected. `CanonNote50`, `CanonNote50Walk`: 0 errors, 0 warnings |
| 25 | Probes on the delivered module | PASS | appended to a copy of the delivered module (imports covered by its own: `Primitives` and `InputCall` are direct imports): `CanonCont4ImportProbe` 130/130, `CanonCont3ImportProbe` 118/118, `B5aContPreShip` 15/15, `CanonNote50Walk`. 0 errors; only the module's two sorry warnings. `B5aStatementsProbe` and `S1210StatementsProbe` import downstream modules (EXPCOM, Relativization, …), so they cannot see the delivery without its olean; run at tip only (statements unchanged) |
| 26 | Note 50 | pending | on the delivered module: 0 errors; `'note50_cases' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]`; walk `note50_cases: [… exists_canonGrammarStage]`. Matches REPORT ("pending") |
| 27 | Lint | PASS | `campaign_style_lint.py TCSlib/Complexity/TuringMachine`: `0 FAIL, 23 WARN over 78 files`; `…/Diagonalization`: `0 FAIL, 0 WARN over 4 files`. Same as tip except the CodeSimulator lines (5257 lines; 11/144). Versus the worker's log, differences only in Catalog, Contract/Catalog and Zone (#108/#109) |
| 28 | Downstream (graph2 at tip) | PASS | 9 modules, import check PASS (list below) |
| 29 | Screen, before (tip) | done | script SHA `f4feac91…f878f181` verified; the 45-file population is byte-equal in both worktrees and is the brief's. `declarations screened: 2393; copy pairs …: 2630; reproduced text: 824,518 chars` (exit 0, 2081 s). Versus the issue-tree base `b5a-fill-canon-cont5-screen-base.txt` (2388/2648/834,815): `new at head 2; earlier-only 20`, all 22 with `Catalog.lean` on a side (#108/#109). The factoring pair `exists_canonStripTM`←`canonPatchWord` 59% is still present (the tip's file is unpatched) |
| 30 | Screen, after (tip + delivery) | PASS | `declarations screened: 2398; copy pairs …: 2629; reproduced text: 824,384 chars` (exit 0, 1722 s). `pairdiff after before`: `new at head 0; earlier-only 1`, the GONE pair being `CodeSimulator.lean::exists_canonStripTM reproduces CodeSimulator.lean::canonPatchWord: 134/229 = 59%` (removed by the prescribed factoring, as intended). No pair names any delivered declaration or either stub. +5 screened declarations: `canonPatchWord_le` plus 4 of the worker's 5; `canonHaltTM`'s body is under the 60-character floor |
| 31 | Comparison with the worker's screens | consistent | worker: before (patched base) 2389/2647/834,681, equal to the published overlay; after 2393/2647/834,681; 0 new, 0 gone. My after vs the worker's after: `new at head 2; earlier-only 20`, exactly the same 22 Catalog pairs as tip-before vs the issue base. The two deltas are identical, so the only difference is #108/#109 in `Build/Catalog` |
| 32 | Size | report | patched base 4,894 lines (11 public / 139 private) → 5,257 (11 / 144) |

## Delivered declarations (REPORT cross-checked against the diff)

| Declaration | Kind | Role | Used by |
|---|---|---|---|
| `canonPatchWord_le` | private lemma | prescribed factoring lemma (from `factor.patch`, unchanged) | `exists_canonStripTM`, `canonPatchWord` |
| `canonSuffixTM` | private def | permitted leaf: native all-`true` suffix scan (blank accepts, `false` rejects) | `canonSuffix_run` only |
| `canonSuffix_run` | private lemma | its contract: first Boolean exit within the remaining length + 1, verdict `List.all id`, output and work tapes and heads preserved, strict cuts | **unused** (it is for the open grammar stage) |
| `canonHaltTM` | private def | permitted leaf: one-step emitting halt | `canonEmitVerdict` |
| `canonHalt_run` | private lemma | exact one-step halt appending the bit (one `simp` with `runFrom_succ_eq_step`, a single step, not a chain) | `canonEmitVerdict` |
| `canonEmitVerdict` | private lemma | three silent strict ports → a halting one-bit computation, `+2` steps, by one public `phaseHostTM` dispatch plus `canonHaltTM` (transported by `runFrom_mapState_of_agreeOn`) | `exists_canonDecider` |
| `exists_canonDecider` | stub → proved modulo the grammar stage | embeds the front end on `C.k` tapes and the grammar's header on front tape 0 (others beyond `C.k`); public seam front `exit true` → grammar; emit adapter on the three ports; degree `a + b + 4` | headline glue |

REPORT's table calls `canonEmitVerdict` a "Public phase-host composition". It means a
composition over the public phase host; the declaration itself is private. No discrepancy.

**Phase reached:** the factoring patch and the inherited phase 2, plus phase-4 work done
conditionally (the validator is proved modulo the open phase-3 stub). Phases 3, 4 and 5 are not
complete. This is a legitimate ground-rule-4 partial: rule 4 says to stop the item and continue
with the rest, and only open frozen stubs remain.

## E1 assessment (verified)

- `counterLoopTM` (`Build/CounterLoop.lean:653`):
  - A successful decrement re-enters the body at `.body a`.
  - When the body's next state is `a`, the host returns to `.dec` (`counterLoopRedirect`).
  - `counterLoopTM_run_done`/`_run_escape` require, per round, start state `some a`,
    positive time, interior avoidance of `a` and the exit, and end state `some a`.
- `exists_canonRecordTM` (C2) gives a run from `d.state = some entry` to
  `some (exit verdict)` with strict exit cuts. It gives no clause about returning to `entry`.
- In the landed construction, `entry = ⟨none, Sum.inr (0, none)⟩` and
  `exit true = ⟨some false, some (some false)⟩`, and `canonRecordNext` redirects the latter to
  itself (stationary). The appended diagnostics prove both facts.
- Hence `a := entry` never returns, and `a := exit true` never parses. A wrapper is needed, so
  the brief's last pitfall bullet ("a counter-loop body can be C2 itself, without a wrapper")
  is wrong.
- The fix the worker proposes uses only public combinators: a `phaseHostTM` adapter with a
  fresh anchor dispatching to C2's entry, with success returning to the anchor and failure
  going to a separate escape.
  - It arguably falls under the brief's own host list ("Compose by the public combinators: …
    the phase host").
  - It costs two dispatch steps per record.
  - It needs an interior-anchor-avoidance contract. That is why the anchor must be fresh: C2
    may revisit `entry` internally.
- The worker escalated rather than build it, given the brief's explicit no-wrapper statement
  and the ban on second hosts. That is conservative and correct under rule 4.

**For cont6** (the adapter is authorized, user 2026-10-16):
- Write the authorization into the cont6 brief: a composition over `phaseHostTM` with a fresh
  anchor, not a new host.
- State its first-return contract (positive duration, interior avoidance).
- Delete the wrong pitfall bullet.
- Keep the generic repetition link "prove once".

## Discrepancies between REPORT.md and my measurements

- None in hashes, commits, counts (5257 lines; 155 declarations; 11/144), axiom prints,
  admission walks, probe results or lint (beyond #108/#109's effect on the lint INFO lines).
- REPORT's sweep (100/100, 46 → 45 sorry declarations, only `exists_canonDecider` removed)
  could not be reproduced here (no oleans of the delivered module). It is consistent with my
  single-module results.
- REPORT notes, correctly, that the 100-module order list
  (`briefs/orders/b5a-fill-canon-cont5.txt`) omits `ClassNP/TMSAT`, which
  `B5aStatementsProbe` imports. The worker checked it separately. This is a maintainer-side
  order-list gap to fix in the next brief's order (TMSAT was present in `oleans-lwalk`, so my
  probe run was unaffected).
- The worker's screens took about 64 and 66 minutes, not the brief's "about 28 minutes". That
  is environment, not a discrepancy.
- Screens: none. The worker's numbers are at the base, mine at the tip; the difference is fully explained by #108/#109 (row 31).

## Duplication

- **New pairs: none**, in both my tip screens and the worker's base screens. No new cross-file
  or in-file pair involves a delivered declaration.
- **One pair removed:** `exists_canonStripTM`←`canonPatchWord` (59%), the user-decided factoring
  (2026-10-15). Its removal matches the pre-ship overlay screen
  (`b5a-fill-canon-cont5-screen-overlay.txt`: 2389/2647).
- The brief's recorded pairs (`scan_grammar_guard`/`canonScan_all` 55%, `canonOffset_spec`, the
  earlier canonizer in-file pairs, the uniform-code mirror pair, item 8's writer pairs) are
  unchanged; nothing is added to them.
- The known hazards (C1/C2 leaves, guard leaves, `codeSkipRepeat_iter`, the H1 loop proofs, the
  R1 reconstruction family) show no new pair.
- "new copies: none" is confirmed.

## Integration notes

- **Cherry-pick, in order:** `899d0796de24827efff274521335a01ca1f4bbab` (prescribed factoring),
  then `7ba42d0f8ee1091a986c34292c7f4c5a59c1aba7` (worker), from `tcslib.bundle` or
  `patches/0001`, `0002`. Both touch only
  `TCSlib/Complexity/TuringMachine/CodeSimulator.lean`, which is unchanged `596cae56`→tip, so
  they apply cleanly.
- **Replay order (graph2, 9 modules):**
  1. `TuringMachine/CodeSimulator`
  2. `Diagonalization/EXPCOM`
  3. `Diagonalization/Relativization`
  4. `Diagonalization` (facade)
  5. `TuringMachine/Codes2Tape`
  6. `TuringMachine/NDCodeSimulator`
  7. `TuringMachine/UniversalK`
  8. `TuringMachine/SelfUniversal`
  9. `TuringMachine` (facade)

  All are under `TCSlib/Complexity/`. Not run here, since no oleans of the delivery may be
  produced.
- **Replay snapshot:** `UniversalK`, `SelfUniversal` and the `TuringMachine` facade import
  `UniversalStartup`, which #110 changed. Replay this list against `oleans-lf3p` (post-#110/#111),
  not `oleans-lwalk`. `CodeSimulator` itself elaborates identically against either, since its
  upstream closure is unchanged.
- **Expected after replay:**
  - `CodeSimulator`: 2 sorry warnings.
  - Base sorry set 46 → 45 (only `exists_canonDecider` removed).
  - Targets 3–8 and `baker_gill_solovay` reach `sorryAx` through `exists_uniformSimulator` and
    `exists_canonGrammarStage` only. This matches the worker's `PublicAxioms.log`.
  - The S1210 control is still detected.
- **Status text to fix at integration:**
  - The `CodeSimulator` module header (lines 71–73) says "Still open: the canonizer's grammar
    loop, its complete validator and the emission". It should now say the validator
    composition and the emission are proved modulo the grammar stage, and only the grammar
    loop is open.
  - The headline keeps its "(spec, fill pending — batch B5a)" tag, which is correct for a
    partial.
  - `Codes2Tape`/`EXPCOM` status: unchanged. The canonizer is still partial; do not mark it
    complete.
  - The grammar-stage appendix says "The brief's no-wrapper claim cannot supply that premise".
    It refers to the brief; consider rephrasing at integration so library text does not cite a
    brief.
- **Unused helper:** `canonSuffix_run` (and `canonSuffixTM`) wait for cont6's grammar stage.
  No warning results.
- **Order-list gap:** add `TCSlib/Complexity/ClassNP/TMSAT` to the next canonizer order list, or
  drop `B5aStatementsProbe`'s TMSAT import from the bootstrap requirement.
