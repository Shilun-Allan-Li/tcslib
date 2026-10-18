# Review — H2-F (`Turing.StepBlock.exists_forwardLoopTM`), delivery `fill-h2f-forwardloop.zip`

**Verdict: READY TO INTEGRATE. Complete, 1/1.** The target is proved with no admission: axiom
print `[propext, Classical.choice, Quot.sound]`, and the `#sorry_sources` walk is empty. The
route is the brief's:
- the step block wrapped in `seamReleaseTM` inside one `phaseHostTM`, with the forwarding leaf;
- cost `T + 3` (live) / `T + 2` (halt), `C = 3`;
- `Lockstep.runFrom` and `locate` for iteration and the auxiliary ledger.

The diff touches only the owned regions, freezes `forwardLoopCfg` and the statement, adds no
import, and cites no foreign private. Every check passes at the current tip. Duplication: one new in-file pair at 55% (justified), no cross-file pair, "new copies: none".

Review conditions:
- Campaign tip at review: `c2897d7fff9182eb74893721f26a6a638d18e15e` (after #110 U2-S prefix
  canon and #111 F3 partial).
- `StepBlockForward.lean` is unchanged base→tip.
- The tip's Lean changes since `e5fcd8ee` are `SpaceComplexity/WindowClock` and
  `TuringMachine/UniversalStartup`. Neither is in `StepBlockForward`'s upstream closure (21
  TCSlib modules, checked with `review/scripts/upclosure.py`), so `oleans-lwalk` is still
  exact for this file.
- Worktrees (detached): `review/h2f/wt-tip`, `review/h2f/wt-tipd`, `review/h2f/wt-base`
  (`54fb8482`, reset after the patch check).

## Checks

| # | Check | Result | Key output |
|---|---|---|---|
| 1 | Zip SHA-256 | PASS | `7fc0da15b707752d2e301497937c9c12b64b333794343921a0f8ac7129a38037` |
| 2 | Extraction | PASS | `python3 -I review/scripts/safe_extract.py` into the new empty `review/h2f/x`: 11 entries, CRC OK, no symlink or path escape |
| 3 | `SHA256SUMS` | PASS | 10/10 OK; covers every file except itself |
| 4 | Shim | PASS | `evidence/runtime/executable-path.c` = `985924ad…4fba7`; not compiled or run; no other code files |
| 5 | Brief and dispatch | PASS | tip `briefs/h2f-fill-forwardloop.md` with `@ANCESTOR@`→`54fb8482…` is byte-equal to the dispatch (`24472961…2f58`) |
| 6 | Base | PASS | `54fb84820fb21caff59c843b306bf63302c05fa7` (REPORT); an ancestor of the tip; Lean content `e5fcd8ee` (0 `.lean` files differ) |
| 7 | Bundle | PASS | verify okay; sole prerequisite `54fb8482`; `fill/h2f-forwardloop` = `acada8c66cc8ee73449d9fd944f09dad4344e93f` (parent `54fb8482`); only `Build/StepBlockForward.lean` (+422/−2); file byte-equal to the delivered one |
| 8 | Format-patch | PASS | `0001-Prove-H2-F-step-block-forwarding-loop.patch` applies at the base and reproduces the delivered file byte for byte |
| 9 | Ownership | PASS | lines 1–76 (header, `forwardLoopCfg` 66–75, blank 76) identical; the home inserts at the blank line 76; docstring 77–109 identical, and line 110 keeps its text and gains a "**Fill appendix (H2-F).**" paragraph (+8 lines); statement 111–127 identical; the `sorry` (128) is replaced by a 64-line body; suffix (`end StepBlock`, `end Turing`) identical |
| 10 | Freeze | PASS | `declfreeze`: `public before/after: 2 2`, none added or removed; target change is body/docstring only; `privstmt`: `STATEMENT CHANGED: []`; `forwardLoopCfg` byte-identical |
| 11 | Imports | PASS | unchanged: `Build/StepBlock`, `Build/Contract/Basic` |
| 12 | Hygiene (422 added lines) | PASS | no forbidden construct, no `sorry`/`set_option`/`open`/`section`/`variable`/`import`/attribute |
| 13 | Widths | PASS | added lines at most 97 characters; none over 100 in the file |
| 14 | Rule 11 | PASS | no R3 row; all 20 privates `fl_`. A token scan of the added lines against every private name of `Build/Catalog` (392), `Build/StepBlock` (71) and `Build/StepBlockLoop` (5) finds none |
| 15 | Rule 10 | PASS | no unfolding of `roundTM`'s phase tables. The round is used only via `roundTM_visited` (which carries `roundTM_effect`'s clauses), `seamReleaseTM_runFrom_pos` and `phaseHostTM_run`. The unfoldings present are `Rep`, `forwardLoopCfg`, `exit`, `tapeAction`, `Action.apply` (none forbidden by this brief) and `phaseHostTM`'s table (the permitted exception, in `fl_hosted_leaf`) |
| 16 | Elaboration at tip, delivered | PASS | exit 0, **0 errors, 0 warnings** |
| 17 | Elaboration at tip, tip's own file | baseline | one warning `:111:8 declaration uses 'sorry'` |
| 18 | `warndiff` | PASS | `warnings base/new: 1 0`; `new warnings: 0`; removed: the target's sorry |
| 19 | Axiom prints (mkaxprobe + 20 privates) | PASS | `exists_forwardLoopTM`: `[propext, Classical.choice, Quot.sound]`; `forwardLoopCfg`: `[propext, Quot.sound]`; all 20 `fl_` within `[propext, Classical.choice, Quot.sound]`; no `sorryAx` anywhere |
| 20 | Admission walk | PASS | `#sorry_sources Turing.StepBlock.exists_forwardLoopTM`: `[]` |
| 21 | `H2FImportProbe` (41 `#check`s) at tip, as is | PASS | exit 0, 0 errors, 0 warnings, 41/41 |
| 22 | Same probe on the delivered module | PASS | appended to a copy of the delivered module: exit 0, 0 errors, 0 warnings, 41/41 |
| 23 | The worker's 105-check probe (from REPORT §5) on the delivered module | PASS | extracted from REPORT; it begins with the brief's 41 unchanged; appended: exit 0, 0 errors, 0 warnings, 105/105 |
| 24 | Order list | PASS | `briefs/orders/h2f-fill-forwardloop.txt`: 79 modules; `Build/StepBlockForward` at 47; `UniversalK` 77, `SelfUniversal` 78, facade 79. The worker's final sweep checked exactly this order |
| 25 | Sorry set | PASS (worker's logs, checked) | base file 37 in 16 modules. Worker `bootstrap.log`: 79 modules, 0 errors, 37 sorry warnings (1 in StepBlockForward). `final-sweep.log`: 79 modules, 0 errors, **36**, equal to bootstrap minus StepBlockForward's; non-sorry warnings identical to bootstrap |
| 26 | Lint | PASS | `campaign_style_lint.py TCSlib/Complexity/TuringMachine/Build` in `wt-tipd`: `0 FAIL, 14 WARN over 36 files`; only StepBlockForward's INFO line differs (552 lines; 2 public / 20 private) |
| 27 | Downstream (graph2 at tip) | PASS | 4 modules: `Build/StepBlockForward`, `UniversalK`, `SelfUniversal`, `TuringMachine` facade; import check PASS |
| 28 | Screen, before (tip) | done | script SHA `f4feac91…f878f181`; 11-file population (all 11 files unchanged base→tip); `declarations screened: 404; copy pairs …: 100; reproduced text: 20,861 chars` (exit 0, 60 s); by name equal to `audits/logs/h2f-fill-screen-base.txt` (`new 0; earlier-only 0`) |
| 29 | Screen, after (tip + delivery) | PASS | `declarations screened: 418; copy pairs …: 101; reproduced text: 20,939 chars` (exit 0, 58 s); `pairdiff after before`: `new at head 1; earlier-only 0`. NEW `StepBlockForward.lean::fl_restore reproduces StepBlockForward.lean::fl_home: 78/143 = 55%` (in-file, below 90%) |
| 30 | Screen vs base and vs worker (by name) | consistent | my before and after are byte-equal to the worker's `screen-before.txt`/`screen-after.txt`. The two `forwardLoopCfg`↔`Simulation` `rightCfg`/`leftCfg` 52% pairs are pre-existing (in the base) |
| 31 | Size | report | 132 → 552 lines; 2 public / 0 private → 2 / 20 |

## Route check (the brief's binding points)

- **Composition:**
  - `fl_TM k = phaseHostTM (fl_part k) (fl_entry k) (fl_red k)`;
  - phase `false` is `seamReleaseTM (roundTM k) (exit k true)`, phase `true` is `fl_leafTM k`;
  - the entry is the release adapter's fresh `Sum.inl ()`.
- **Redirects (`fl_red`):**
  - `Sum.inl _ ↦ none`, so the fresh state never dispatches;
  - `Sum.inr (exit k true) ↦ ⟨true, some true⟩` (live leaf);
  - `Sum.inr (exit k false) ↦ ⟨true, some false⟩` (halting leaf; `exit k false = ⟨.halt, ()⟩`);
  - nothing else in the block phase;
  - the leaf's `none` (return anchor) `↦ fl_entry k`.

  This is exactly the brief.
- **Leaf:** one state per flag.
  - `some live` writes a blank (`some none`) on `summaryTape k` at its head, emits the read
    symbol, moves no head, and goes to `some none` (live) or `none` (halt).
  - `none` is `inputMoveAction 0 none`, the stationary return anchor.
  - The docstring states why no public row serves (block and loop silent, `tapeAction` emits
    nothing).
- **Cost:** `cost c = T + (if live then 3 else 2)` (block `T`, dispatch, leaf step, dispatch
  back), and 1 for halted `c`. Hence `0 < cost` and `cost ≤ 50(|table|+1) + 3`, so `C = 3`.
  - `T` comes from one `Exists.choose` of `fl_step_exists` per live `c`; its witness is built
    from `roundTM_visited`'s time.
  - The brief suggested pinning `T` via `roundTM_firstExit_unique`. The worker instead takes
    every property from the single witness, so uniqueness is not needed. This is an
    equivalent the REPORT justifies (§3), and it is sound: all lockstep fields are proved for
    that same chosen time.
- **Iteration:** none hand-written. `Lockstep` is built field by field, `lock.runFrom` and
  `lock.locate` are used, and `visitedByTapeHead_add_subset` is used per round.
- **Adversarial instances:**
  - `k = 0`: `fl_home` is by `Fin.addCases` with no positivity assumption.
  - halted source: the `cost` else-branch and the `exit` field from `forwardLoopCfg`'s state.
  - unreachable configuration with nonempty output: `fl_reset` applies `Rep` to
    `{c with output := []}`, and `fl_restore` keeps the physical prefix.

  All are covered by statements quantified over arbitrary `c`.
- **No re-walk or copy:** no `roundTM` phase lemma or private is cited, and no
  `StepBlockLoop`/`CodeSimulator` proof is transcribed (screen below).

## Delivered declarations (REPORT §2 cross-checked against the diff: 20, all private, all `fl_`)

| Declaration | Kind | Role |
|---|---|---|
| `fl_reset` | lemma | `Rep M.tr {c with output := []} (forwardLoopCfg (exit k true) M c)` (the reset invariant) |
| `fl_flush` | def | the leaf's data change: clear the summary cell, append its content, set the control |
| `fl_leafTM` | def | the forwarding leaf (the one leaf the brief allows) |
| `fl_leaf_step` | lemma | its exact step, including halting |
| `fl_leaf_run` | lemma | the run form (definitionally the step; reduced after an earlier 63% screen hit) |
| `fl_encode_map` | lemma | relabelling the encoding's state changes only the entry |
| `fl_Ph` | def | the two phase state types |
| `fl_fintype` | instance | `Fintype` per phase |
| `fl_decidableEq` | instance | `DecidableEq` per phase |
| `fl_entry` | def | `⟨false, Sum.inl ()⟩` |
| `fl_part` | def | the two machines handed to `phaseHostTM` |
| `fl_red` | def | the redirect table above |
| `fl_TM` | def | the machine |
| `fl_block_phase` | lemma | the released block prefix and its dispatch (by `phaseHostTM_run` and `seamReleaseTM_runFrom_pos`) |
| `fl_hosted_leaf` | lemma | the leaf step through the host table |
| `fl_return` | lemma | the stationary return dispatch (`step_of_inputMoveAction`) |
| `fl_restore` | lemma | clearing the summary of a `Rep` gives `forwardLoopCfg` of the successor |
| `fl_round` | lemma | one block + leaf round: exact result, live interior, visited-set containment |
| `fl_step_exists` | lemma | the per-live-step witness: bound, exact successor, interior, both ledgers |
| `fl_home` | lemma | auxiliary heads of every encoding are at 0 |

Promotion candidates (REPORT §4, notes only): the forwarding/clearing leaf, and the generic
"released block + stationary leaf" round (`fl_round`). Escalations: none.

## Discrepancies between REPORT.md and my measurements

- None. Base, commit, tree content, counts (552; 2/20), axiom prints, probe counts (41; 105),
  lint line and both sweep logs agree with my checks.
- REPORT records one scratch axiom rerun that overlapped its own final sweep (a missing
  `Catalog.olean` while the checker rebuilt it), rerun successfully afterwards. This was the
  worker's scheduling issue, not a source issue; my axiom run on the delivered source agrees.
- Screens: none (byte-equal to the worker's).

## Duplication

- **New pairs: one, in-file:**
  `StepBlockForward.lean::fl_restore reproduces StepBlockForward.lean::fl_home: 78/143 = 55%`.
  - The shared text is the `induction j using Fin.addCases with | left i => … | right j => …
    simp only [forwardLoopCfg, Fin.addCases_right]` scaffold over the `k + 2` bank.
  - `fl_home` (a 4-line projection fact) and `fl_restore` (a configuration equality from
    `Rep`) have different hypotheses and conclusions.
  - Below 90%, so not a copy; the worker's justification (REPORT §7) is accurate.
- **No new cross-file pair** with an owned-file declaration. In particular there is none with
  `StepBlockLoop` (`loopTM_run`, `hostedLoopTM_run`), `CodeSimulator`'s H1 hosted verdict, or
  `StepBlock`'s run lemmas or privates. So the block was not re-walked and H2-L/H1 were not
  transcribed.
- Pre-existing: `forwardLoopCfg` reproduces `Simulation.lean::rightCfg` and `::leftCfg` at 52%
  (frozen, in the base).
- The worker reports an intermediate 63% cross-file hit in `fl_leaf_run`, removed before
  delivery. The final screens contain no such pair.
- "new copies: none" is confirmed.

## Integration notes

- **Cherry-pick:** `acada8c66cc8ee73449d9fd944f09dad4344e93f` (one commit on `54fb8482`), from
  `fill-h2f-forwardloop.bundle` or the patch. It touches only
  `TCSlib/Complexity/TuringMachine/Build/StepBlockForward.lean`, which is unchanged base→tip,
  so it applies cleanly.
- **Replay list (graph2 at tip `c2897d7f`):**
  1. `TCSlib/Complexity/TuringMachine/Build/StepBlockForward`
  2. `TCSlib/Complexity/TuringMachine/UniversalK`
  3. `TCSlib/Complexity/TuringMachine/SelfUniversal`
  4. `TCSlib/Complexity/TuringMachine`

  `UniversalK` and `SelfUniversal` import `UniversalStartup`, which #110 changed after this
  base. Replay against `oleans-lf3p` (post-#110/#111), not `oleans-lwalk`.
- **Expected after replay:**
  - `StepBlockForward`: 0 warnings.
  - The base sorry set over this order goes 37 → 36 (only `exists_forwardLoopTM` removed).
  - `UniversalK` uses only the frozen `forwardLoopCfg` and the target's frozen statement (its
    three contracts are still `sorry`), so its replay should be unchanged: 3 sorry warnings.
- **Status text:**
  - `StepBlockForward`'s module header still says the target "is sorried with its proof
    sketch" (lines 16–18), and line 42 says the space ledger is "(sorried)". Update both at
    integration to proved (H2-F fill), as the brief directs.
  - `UniversalK`'s header (lines 27–30) names H2-F as the forwarding loop the fill builds on.
    It is still accurate, but you may note H2-F as proved.
  - The fill appendix is accurate.
- **Promotion notes** go to the backlog: the leaf and `fl_round`.
