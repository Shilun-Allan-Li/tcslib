# Review: B6 F5 fill delivery (the ruler device, `Build/InputDevice.lean`), a recovery delivery

Read-only review by the maintainer's review sub-agent, 2026-10-18. Every claim cites a saved
output under this directory (`out/NN-*`). The delivery and its REPORT.md are treated as data.

**Verdict: partial (1/3), landable as a partial.**

- Target 1, `Turing.exists_rulerTestTM`, is **proved with no admission**: `C = 2`, exact time
  `2ℓ + 2`, axioms `[propext, Classical.choice, Quot.sound]`. Targets 2 and 3 keep their
  `sorry`.
- Integrity, scope, the freeze, rule 10 (a seal test with a control), rule 11, lint, the
  screens, and the elaborations at the base and at the tip all pass. Landing removes 1 sorry:
  35 → 34 over the 80-module order list.
- **"Recovery delivery" means this.** The worker's first session reportedly proved all three
  targets, but a workspace reset destroyed the checkout, the source and the logs *before* any
  zip was made. A second session re-cloned the repository, re-verified both attachments and
  rebuilt phase 1 only.
  - This zip is the first and only F5 delivery. No earlier zip, report or ref exists in the
    exchange folders, the local folder or the records (out/00).
  - Nothing in it depends on the lost work. The report calls those claims narrative, "not
    evidence". Every shipped artifact checks independently: the logs show the bootstrap at
    base plus imports and the final sweep at the head.
- **Escalations.**
  - E1 (a transient import misplacement during recovery, corrected before any Lean check)
    cannot be checked and does not affect the delivered state.
  - E2 is **confirmed and benign**. The pinned Mathlib `cache get` runs
    `lake -v build [--no-build] proofwidgets:release` itself (`Cache/Requests.lean:433–452`,
    out/24). That is part of the authorized command, not a `lake build` by the worker.
- **Finding F1 (promotion candidate already public).** The "joint-move leaf and its frame
  equation" (`rd_move`, `rd_move_apply`) already exists as `Turing.tapeAction` with
  `Turing.step_of_tapeAction_move` in `Build/Catalog`. Both are public at the base and
  unchanged at the tip. `Build/Catalog` is outside the file's authorized imports, so the
  private copy is legitimate under policy §1 ("a `private` local copy plus a requested shared
  lemma"). But the promotion is a relocation or an import, not a new public leaf. This review
  checked the import variant: 0 errors under a seal that includes `tapeAction`, clean axioms
  (out/46).
- **F2 (text to reword at landing).** The three "Fill appendix (B6-F5)" paragraphs are not
  public-facing. Rewordings are in (e).

## Inputs

| Input | Identity | Evidence |
| --- | --- | --- |
| Zip `exchange/inbox/fill-b6-rulerdevice.zip` | SHA-256 `65fa6ff7…b17d`, 11 entries, no unsafe entry, CRC OK | out/01, out/02 |
| Extraction `$S/incoming/b6-rulerdevice/` | every member byte-equal to the zip | out/02 |
| `SHA256SUMS` | 10/10 OK; covers every member except itself | out/03 |
| Brief (dispatch copy) `exchange/archive/fills/b6-fill-rulerdevice.md` | `e181d7e2…49b4`, equal to REPORT's. It equals the base's `briefs/b6-fill-rulerdevice.md` after `@ANCESTOR@` → base; the records copy `campaign/fills/b6/briefs/` is the unsubstituted base file. | out/04 |
| Addendum v1 | `a25474c5…2928`, equal to the base's `briefs/fill-environment-addendum.md` and to REPORT's (attached as "…addendum(8).md"). The delivered `executable-path.c` is byte-equal to its code block, `985924ad…`. | out/04 |
| Base `94b986d4db7167ab2a8b20d38d4385f11e60be0e` | parent `f7546373`; TCSlib tree `11fcef24` = `531b98a2`'s = `f7546373`'s | out/04 |
| Tip | `origin/complexity/arora-barak-ch3-4` = `2df1add6` (`$S/wt-hk`); TCSlib tree `06d30610` = `5fd5dce8`'s | out/23 |
| Snapshots | `oleans-lbapi4` (base), `oleans-lx2b` (tip; provenance per the caller) | — |

Review worktrees, all detached under this folder, each with the `.lake/packages` link:
- `wt-base`, the base;
- `wt-head`, the head `f9810ddf`;
- `wt-tipd`, the tip `2df1add6` with the delivered patch applied (uncommitted).

The bundle head was fetched into `refs/review/b6-f5`. Lean ran only through `tools/leanelab.sh`,
one elaboration at a time. No build or cache command was run, and the shim was neither compiled
nor run. Probes are in `probe/` (copies of `wt-*/ReviewProbe/*.lean`) and scripts in `scripts/`;
their hashes are in out/43. The main repository's working tree and branches are untouched.

## (a) Integrity and scope

| # | Check | Result | Evidence |
| --- | --- | --- | --- |
| 1 | Bundle | `verify` okay. One ref, `refs/heads/fill/b6-rulerdevice` = `f9810ddf411ebb40b07e287398787d0db4e160f6`, the hash REPORT gives. Its sole prerequisite is the base. | out/05 |
| 2 | Head commit | one commit; sole parent exactly the base; author "Codex"; changes only `Build/InputDevice.lean` (+222/−4) | out/06 |
| 3 | Patch | applied at the base in a temporary index, it gives the head tree `2679490a`. It equals `git format-patch -1` of the head except for the trailing git-version line (`2.51.1` vs the local one). | out/07 |
| 4 | Delivered file | byte-equal to the head blob `1785a92b` (SHA-256 `fa347689…f5ce`) | out/08 |
| 5 | `git diff --check` | clean | out/09 |
| 6 | Owned regions | 4 removed and 222 added lines, all in the regions. Region (a): 2 imports before base line 8. Region (b): 170 lines at home 202 only; homes 228 and 281 are unused. Region (c): target 1's `sorry` (227) only. Region (d): the three closers (215, 248, 312). There are 0 lines outside. | out/16 |
| 7 | Reversal | dropping the two imports, the private block and the three appendices (re-attaching ` -/`), and restoring target 1's `sorry`, gives the base byte for byte. (`stmtcheck.py`'s 51 "missing" lines are its known in-order cascade: base line 227's `sorry` matches head line 482's.) | out/17, out/15 |
| 8 | Freeze (`declfreeze.py`) | 15 public before and after; none added or removed; no `STATEMENT CHANGED`; body/docstring changes only in the three targets (authorized). 11 privates added, all `rd_`. | out/13, out/14 |
| 9 | Imports | exactly `Build.Contract.Basic` and `Build.Seam`, after line 7, the original order kept | out/10 |
| 10 | Hygiene (added lines) | no `sorry`, `admit`, `axiom`, `unfold`, `set_option`, `open`, `section` or attribute. One `decide` is a definition body (`rd_verdict`); one `by decide` proves `yes ≠ no` on `Unit ⊕ Bool × Bool`. | out/18 |
| 11 | Widths, style | added lines at most 94 characters; no file line over 100; no trailing whitespace. **Nit:** three consecutive blank lines at 372–374 (after `rd_run`), and `rd_trace_step`'s docstring has no blank line before its "Proof sketch". | out/18 |
| 12 | Rule 11 | 0 R3-row hits. The four lexical private-name hits (`S`, `add`, `one`, `test`) are a bound type variable and prose words. The compiled walk finds no external private (row 17). | out/42, out/19 |
| 13 | Size | 339 → 557 lines; 15 public / 11 private | out/37 |
| 14 | Recovery | no other F5 zip, report or ref exists (out/00). The bootstrap log shows `InputDevice` at 218/251/315, i.e. the overlay (base plus the two imports), so the base list was measured before any helper existed; that is consistent with E1's account. The final sweep is at the head (461/531). | out/00, out/38 |

## (b) Elaboration and axioms

| # | Check | Result | Evidence |
| --- | --- | --- | --- |
| 15 | Base file against `oleans-lbapi4` | exit 0; sorry warnings at 216, 249, 313 (the three) | out/11 |
| 16 | Head file against `oleans-lbapi4` | exit 0; sorry warnings only at `461:8` (target 2) and `531:8` (target 3); no error, no other warning | out/12 |
| 17 | Axioms, admission and dependency walk (a scratch copy with prints) | **Target 1: `[propext, Classical.choice, Quot.sound]`, no `sorryAx` source in its closure.** Targets 2 and 3 carry `sorryAx`, and each is its own only source. The 11 privates are within the standard three; `rd_State`, `rd_move` and `rd_verdict` use none. No external private and no other-file equation lemma is reached. (The tool's `Bool.eq_iff_iff` hit is a name-pattern false positive.) This agrees with the worker's `axioms.log`. | out/19 |
| 18 | TCSlib constants reached | 40, all public at the base (`Action`/`Cfg` structure and field lemmas, `step_of_some`, `runFrom_zero`/`_succ_eq_step'`, `bufferTape_nat`/`_left`, the `moveInputPos` lemmas, `inputSymbolInner`). They are all in REPORT's 368-name inventory, which also lists `Cfg.workTapeSymbols_eq`: simp uses that rfl-lemma without recording it in the term. 33 of the 40 are outside the brief's 58-name probe (structures, projections, field lemmas, `_proof_` auxiliaries). | out/20, out/20b |
| 19 | Import probe | the brief's 58 checks, plus 16 other-file TCSlib names and 37 core/Mathlib lemmas the proofs cite, run against the delivered file: 111 checks, 0 errors; the only warnings are the two open targets' sorry warnings | out/22 |
| 20 | Rule 10, seal test | nine other-file definitions made `local irreducible` around the private block and target 1: `MultiTapeTM.step`, `runFrom`, `outputSymbol`, `Action.apply`, `moveInputPos`, `FinTM.bufferTape`, `Cfg.inputSymbol`, `Cfg.workTapeSymbols` and `Cfg.init`. Result: 0 errors, the same two warnings. **Control:** inside the seal, `((rd_move none 0 0).apply d).state = none := by rfl` fails; outside it, it succeeds. So the seal is in force. | out/21, out/21b |
| 21 | Worker's sweep logs | bootstrap and final: 80/80, in the order list's exact order, 0 errors. Bootstrap: 35 sorry warnings in 15 modules, the base list by name. Final: 34; only `exists_rulerTestTM` is gone. All 405 other diagnostics (file, line, column, kind, first line) are identical. | out/38, out/38b |

## (c) Progress

| Target / phase | State | Notes |
| --- | --- | --- |
| Phase 1: `exists_rulerTestTM` | **proved** | witness `rd_test` on `Unit ⊕ Bool × Bool`; `yes = inr (true, true)`, `no = inr (false, true)`; `C = 2`; `t = 2ℓ + 2` |
| Phase 2: `exists_rulerDeviceTM` | open | base Proof sketch kept; appendix sketch added |
| Phase 3: `exists_rulerHostTM` | open | base Proof sketch kept; appendix sketch added |

- **The route is the brief's.** `rd_test` is a leaf with one forward state and return/verdict
  states carrying the verdict bit.
  - Forward leg (ℓ joint moves): input left, ruler right.
  - Turn (at the blank after the ruler): reads `inputCell z (p − ℓ)` and records `isNone`
    through `inputCell_sub_eq_none_iff`.
  - Return leg (ℓ joint moves): input right, ruler left. Then the left delimiter, and one
    step right.
  - `rd_trace` names every point of the trajectory, and `rd_run` is its single induction.
    The four cases of `rd_trace_step` are interior forward, turn, interior return and left
    delimiter.
- **The proof matches the target's docstring** (the base sketch, binding). The gate's instances
  (ℓ = 1, an empty payload, the physical head at the right blank) are covered by the general
  statement: `p ≤ |z| + 1` comes from `inputPos.isLt`, so no extra hypothesis is needed.
- **Rule 10.**
  - Machine steps are read only through `step_of_some`, `runFrom_zero` and
    `runFrom_succ_eq_step'`.
  - Applied actions are read only through `Action.apply_state`, `_inputPos`, `_workTapePos`,
    `_output` and `_workTapes`.
  - Input moves are read through `moveInputPos_zero`, `_neg_of_ne_left` and
    `_pos_of_ne_right`.
  - The only definitions unfolded are the file's own (`rd_*`, `inputCell`). The seal confirms
    this (row 20).
- **Rules 3, 7 and 9.**
  - No new public declaration.
  - One trajectory and one induction.
  - The partial states the phase reached, gives each open target a literal Proof sketch, and
    prints each target's axioms. Every inserted helper is proved: no admission in any `rd_*`.
- **REPORT's continuation figures are plausible but unchecked:**
  - device: `2ℓ + 5 ≤ 4(ℓ + 1)` for `ℓ ≥ 1`;
  - host: `1 + (2ℓ + 2) = 2ℓ + 3 ≤ 3(ℓ + 1)`.
- **Usable by the continuation.** The test's hypotheses are exactly `RulerAt ℓ 0 d i`'s last
  conjunct, and `ℓ ≤ inputPos` follows from `inputPos = ℓ + i`. So target 2 can call target 1,
  or `rd_run`, directly.

## (d) Escalations and promotion candidates

**E1 (transient import placement).** The imports were first written after line 6, then moved
after line 7 before any Lean check.
- This cannot be checked from the zip. It is consistent with the bootstrap's line numbers
  (row 14), and the delivered placement is exact (row 9).
- Ruling suggested: accept as disclosed; no action.

**E2 (Lake inside `lake exe cache get`): true at the base and at the tip.**
- The pinned Mathlib `029db123` (base and tip manifests; the local package checkout is clean)
  has `getProofWidgets` in `Cache/Requests.lean`. It runs `lake -v build --no-build
  proofwidgets:release`, then, if a fetch is needed, `lake -v build proofwidgets:release`
  (out/24).
- Every `cache get` does this, so every earlier fill run did too. It is not a breach of
  "never `lake build`".
- Suggested: one sentence in the addendum and the brief template saying so (decision 2).

**Workspace loss.** This is the recovery's obstruction, not an escalation about the
mathematics. No missing lemma or false statement is claimed, and this review found none.

**Promotion candidate 1: the joint-move leaf and its frame equation (`rd_move`,
`rd_move_apply`).** It is true and proved at the base (row 17), and still at the tip ((f), out/29).
**But its general form is already public (F1):**
- `Turing.tapeAction i inp wr m q` is in `Build/Catalog.lean:11685`, unchanged base → tip
  (out/00). It is `⟨inp, fun j => if j = i then (wr, m) else (none, 0), none, some q⟩`, at
  `k = 1, i = 0, wr = none` exactly `rd_move (some q) inp m`.
- `Turing.step_of_tapeAction_move` is in the same file, `:11702`. It gives `M.step c` as
  `{c with state, inputPos := moveInputPos c.inputPos inp, workTapePos := update …}`.
- REPORT's sentence "the catalog moves work heads or the input head separately" is accurate for
  catalog *rows* (as the brief says), but not for the catalog's action layer.
- `Build/Catalog` is not in `InputDevice`'s import closure. The brief fixes exactly two imports,
  so the private copy is the policy-conforming choice.

**Probe of the alternative** (`probe/B6F5TapeAction.lean.txt`, diff `probe/tapeaction-variant.diff`):
- **Changes:** a third import, `Build.Catalog`; `rd_move` and `rd_move_apply` deleted (−21
  lines, −2 privates); `rd_test`'s table written with `tapeAction 0 …`; `rd_cfg_step` closed by
  `step_of_tapeAction_move` plus `Subsingleton.elim i 0` and `Function.update_self`.
- **Result:** 0 errors, with `tapeAction` added to the seal. Target 1 prints
  `[propext, Classical.choice, Quot.sound]` (out/46).
- **Import cost:** the import adds 4 modules to `InputDevice`'s upstream closure. All four are
  already upstream of `UniversalK` and `SelfUniversal`, so nothing new becomes visible
  downstream.

**Promotion candidate 2: a generic "host step plus a pause" lockstep lemma.** It is not
delivered (REPORT says so); it is for phase 3. No public form exists to compare against.

**REPORT's other claims, spot-checked.** All hold:
- 557 lines, 15 public / 11 private (row 13);
- the axiom walks (row 17);
- "only public declarations at the pinned base" (rows 17–18);
- the probe re-run (row 19);
- 35 → 34 sorries (row 21);
- the lint and screen results ((e)).

## (e) Duplication and lint

The v3 screen script's SHA-256 is `f4feac91…f181` at the base, the head and the tip (out/36).

| # | Check | Result | Evidence |
| --- | --- | --- | --- |
| D1 | Before (base, the 11-file population) | `272 declarations; 138 pairs; 31,217 chars`, exit 0. Byte-equal to `audits/logs/b6-fill-rulerdevice-screen-base.txt` (comments stripped) and to the worker's `screen-before.txt`. | out/39, out/45 |
| D2 | After (head) | `281; 139; 31,290 chars`, exit 0; byte-equal to the worker's `screen-after.txt` | out/40, out/45 |
| D3 | New pairs (`pairdiff.py` against the before screen and the base log) | **1 new, 0 removed**: `InputDevice::rd_trace_step reproduces rd_read_nat: 73/90 = 81%`. It is in-file and below 90%. The worker's justification holds: the turn case's `hend` repeats `rd_read_nat`'s two-line `bufferTape_nat`/`getElem?_replicate` lookup, at the delimiter. No cross-file pair touches the owned file, and none of the known hazards (Z1's host proofs, `universalInput_read`/`_move`, the unary marker) pairs with it. **"New copies: none" is confirmed** at text level. The F1 semantic overlap with `Build/Catalog` is outside the population and is not a text copy (different proof). | out/45 |
| D4 | Discipline | both screens ran one at a time under `nice -n 10`, each started only when `pgrep -f copy-text-screen-v3` found none (`scripts/screens.sh`) | out/39–40 `.status` |
| L1 | Lint `TuringMachine/Build` (base script) | base and head `0 FAIL, 32 WARN over 37 files`; non-`InputDevice` lines identical; `InputDevice` 339 → 557 lines, 15/0 → 15/11; head output equal to REPORT's block | out/37-lint-base, -head |
| L2 | Lint (tip script `65c420ea`) | tip and tip+patch `0 FAIL, 30 WARN over 37 files`; only the `InputDevice` INFO line differs | out/37-lint-tip, -tipd |

**F2: delivered text that is not public-facing** (the user's 2026-10-17 preference). The brief
prescribed the "Fill appendix (B6-F5)" label, so this is a landing edit, not a worker fault.
Suggested public-facing replacements for the maintainer's landing commit:

- **Target 1's appendix** (it has the label "B6-F5" and the campaign phrase "the published
  boundary fact"). Replace with:

  > **Implementation.** The test is a hand-built controller that moves the input head and the
  > ruler head in the same step; no catalog row does that (the action has the shape of
  > `Turing.tapeAction`). One forward-and-return trajectory, identified by a single induction,
  > takes exactly `2ℓ + 2` steps, so `C = 2`. The turn reads the boundary through
  > `Turing.inputCell_sub_eq_none_iff`; the return leg changes no tape and no output and
  > restores both heads.

- **Targets 2 and 3** ("B6-F5", "Open in this partial delivery", "R1"). Preferably **delete
  both appendices**: the base docstrings already carry the binding Proof sketch the linter
  needs, and the open status belongs in the module's status text. If a route note is wanted,
  use the following.
  - Target 2:

    > **Route.** Run the boundary test of `Turing.exists_rulerTestTM`, then a one-step read or
    > move leaf, joined by the phase host (`Turing.phaseHostTM_run`); the two rows share the
    > phase argument, and the read row's answer is `Turing.inputCell_of_drop`.

  - Target 3:

    > **Route.** Build the one-step source transformer carrying the boundary tag, and run the
    > test on the last tape through the silent embedding (`Turing.embedSilentTM`). A host step
    > with its optional pause is a `Turing.Lockstep`; `Turing.Lockstep.runFrom`, `.cut` and
    > `.locate` give the endpoint, the exit cut and the frames, from which the space clauses
    > follow.

- **Private docstrings.**
  - `rd_move`: "A silent action moving the input head and the work head together (the shape of
    `Turing.tapeAction`)." Drop it entirely under decision 1(ii).
  - `rd_test`'s second sentence: "No catalog row moves the input head together with a work
    head."

  Both are otherwise fine.
- **Module status text** (base text; the maintainer updates it at integration).
  - Mark `exists_rulerTestTM` proved in "Main results" and in "Status".
  - The status line cites `audits/b6-hosts-statements-findings.md`. That path is stale since
    the restructure (now `campaign/gates/13-b6-hosts-statements/findings.md`) and is not
    public-facing. Drop the path.

## (f) Landability

- **The owned file is unchanged from base to tip.** Its blob is `1cc06602` at both, and no
  commit in `94b986d4..2df1add6` touches it (out/23). The patch applies cleanly at the tip,
  giving the delivered file byte for byte (out/25).
- **Imports.** The upstream closure (15 modules) is the same at the head and at tip+patch
  (out/26). Four upstream modules changed, all by addition only: `Build/Convention` +23,
  `Build/VirtualInput` +25, `Encoding` +52, `Simulation` +25 (out/27). No cited declaration
  changed. The two new imports expose nothing new downstream: `UniversalK`, `SelfUniversal` and
  the facade already import both (out/35).
- **Elaboration at the tip** (`wt-tipd` against `oleans-lx2b`): exit 0, only `461:8` and
  `531:8` (out/28).
  - The axiom, admission and dependency probe is identical to the base-snapshot run (out/29).
  - The seal test is clean (out/30).
  - The 111-check import probe is identical to the base-snapshot run (out/31).
- **Replay closure at the tip** (`mkdownmulti.py`): `Build/InputDevice`, `UniversalK`,
  `SelfUniversal`, then the `TuringMachine` facade (4 modules; out/32). All 82 of their imports
  have oleans in `oleans-lx2b` (out/33). Do not append the root `TCSlib`.
- **Overlap with the open PRs' replay closures** (computed from each PR head's own tree;
  out/34). No PR touches `InputDevice.lean`.

  | PR | Changed | Overlap with F5's closure |
  | --- | --- | --- |
  | #124 | facade, `SeamLayout` | the facade |
  | #129 | `NTimeHierarchy` | none |
  | #130 | `UniversalK` | `UniversalK`, `SelfUniversal`, facade |
  | #131 (on #130) | `CodeSimulator`, `UniversalK` | `UniversalK`, `SelfUniversal`, facade |
  | #132 | `Primitives`, `Simulation` | all four (`Simulation` is upstream of `InputDevice`) |

  The order is free. In either order the later PR replays its own closure into the snapshot
  left by the earlier one. F5's closure is 4 modules; #132's is 313 and includes
  `InputDevice`.
- **Expected sorry count after landing:** −1. The module's count goes 3 → 2.

## (g) Recommendation

**Not yet clear to merge.** The landing PR is still to be opened, replayed and gated.

**Land as a partial: yes**, by a maintainer PR on the tip.
- **Commit.** Cherry-pick `f9810ddf411ebb40b07e287398787d0db4e160f6` from `refs/review/b6-f5`;
  its prerequisite is `94b986d4`. It touches only the owned file.
- **A maintainer commit on top:**
  1. F2's rewordings: replace target 1's appendix; delete, or reword, targets 2–3's appendices;
     reword the two private docstrings.
  2. The module's status text and "Main results": target 1 is proved, and the stale `audits/`
     path goes.
  3. Style nits: collapse the blank lines at 372–374, and add a blank line before
     `rd_trace_step`'s Proof sketch.
  4. If decision 1(ii) is taken, apply `probe/tapeaction-variant.diff` (minus its seal section
     and `#print`).

  Then re-elaborate (expect `461:8`/`531:8`, shifted only if lines move), re-lint and
  re-screen.
- **Replay:** `Build/InputDevice`, `UniversalK`, `SelfUniversal`, the `TuringMachine` facade,
  into a copy of `oleans-lx2b`.

**Decisions for the user:**
1. **The joint-move leaf (F1).** Choose one:
   - **(i)** Keep the private `rd_move`/`rd_move_apply`, naming `Turing.tapeAction` in the
     docstring. The promotion candidate is then recorded as already served by `tapeAction`.
   - **(ii)** Authorize `import TCSlib.Complexity.TuringMachine.Build.Catalog` in
     `InputDevice` and use `tapeAction`/`step_of_tapeAction_move`. Verified (out/46), and it
     removes two privates.
   - **(iii)** Move `tapeAction`, `inputMoveAction` and their step lemmas to a lower shared
     module in an API PR, so that `InputDevice` and the call rows can cite them without
     `Catalog`.

   The continuation's read and move leaves (phase 2) need the same action shape, so whichever
   is chosen should be fixed before that brief. (ii) is the smallest; (iii) is the cleanest
   layering.
2. **E2.** Add to the environment addendum and the brief template one sentence saying that
   the pinned `lake exe cache get` runs `lake build [--no-build] proofwidgets:release`
   internally, that this is part of the authorized command, and that it needs no escalation.

**The F5 continuation brief should:**
- re-base after the landing (target 1 proved; `rd_test`, `rd_run` and `rd_trace` available
  in-file);
- fix decision 1's leaf for the read/move one-step leaves;
- keep phases 2 and 3 as they are, with the gate's instances for targets 2–3 (the clamped
  right move at `i = |y| + 1`; no pause after a halting left move);
- ask for a checkpoint zip after each phase. The lost first session cost two of three proved
  targets.

**Environment (brief).**
- Unmodified Lean failed ("failed to locate application"), and the addendum's shim
  (`985924ad…`, matched) was used. The variables are recorded.
- `TAR_OPTIONS=--no-same-owner` was used for the toolchain extraction and for the cache retry.
- The cache was fetched only for the 35 direct Mathlib imports. No `lake build` was issued by
  the worker; E2 covers the internal call.
