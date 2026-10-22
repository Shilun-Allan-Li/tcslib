# Review — B6, F5 continuation 1: the ruler device's call rows and host (`Turing.exists_rulerDeviceTM`, `Turing.exists_rulerHostTM`, `Build/InputDevice.lean`), delivery `fill-b6-rulerdevice-cont1.zip` (megafill B, item 2)

Read-only review by the maintainer's review sub-agent, 2026-10-22. Every claim cites a saved
output under this folder (`out/NN-*`). The delivery, its REPORT.md and the megafill's session
report are treated as data.

**Verdict: complete (2/2; the module has no admission left). Land, with the maintainer's
landing edits in (h).** Both open targets are proved, and the restoring test stays proved and
frozen:
- The head module elaborates with 0 errors and 0 warnings, at the base and at the tip with the
  series applied (out/18, out/41).
- All three targets depend on `[propext, Classical.choice, Quot.sound]`, and nothing in their
  closures uses `sorryAx` (out/20, out/21).
- **The call rows:** one phase host runs the test, a one-step `inputMoveAction` leaf and a final
  dispatch. Exactly `2ℓ + 5` steps, so `C = 4`.
- **The host:** a `Turing.Lockstep` over `rulerHostCfg` with the tag `c.inputPos = 0`. A block
  costs `1`, or `2ℓ + 3` after a live left move from a cleared tag, so `C = 3`.
- The REPORT's claim "device and host proved without admitted dependencies" holds.

What passes:
- integrity (92/92 sums; the bundle, sole prerequisite the base; 2 linear commits; patch series =
  bundle = delivered file);
- scope:
  - four hunks, all in the owned regions (the two homes, the two `sorry`s);
  - the three statements and both open targets' docstrings byte-identical to the base;
  - 32 new privates, all `rd_`; no new public declaration; imports unchanged; no admission;
- 56 axiom prints, equal to the worker's 35 on every common name;
- rule 10:
  - a 17-definition seal, with the two `@[simp]` defs erased from the simp set;
  - 0 diagnostics in the body, and all 38 controls bite at the top and at the end of the seal;
  - no other-file definition among the 376 `rw`/`simp`/`unfold` arguments;
- rule 11;
- the brief's 62-check probe and the worker's 148-check probe, 0 errors each, also against the
  delivered module;
- **the gate's adversarial instances, by running the delivered machines** (24 runs, out/30):
  `ℓ = 1`, `z = [true]`, `y = []` at both positions; the empty payload at `p = |z| + 1`; the
  clamped right move at `i = |y| + 1`; a source halting on a left move; zero bank tapes; an
  initially halted source;
- the v3 screen: 720 → 741 declarations and 488 → 489 pairs. The one new pair is in-file, at
  79%; there is no cross-file pair and none at 90% or more. Equal to the worker's;
- lint 0 FAIL (the one new WARN is the file size);
- the worker's 95-module sweep (33 → 31, the two targets only; every other diagnostic identical).

Findings (none blocks landing):
- **F1 (docstrings, a landing edit).** The two frozen proof sketches name routes the proofs do
  not take. Policy §3 ("Synchronization") asks the docstring to describe the proof the code
  performs.
  - Target 2's sketch ends "Rows are joined by R2 seams". The proof uses the phase host,
    `phaseHostTM_run`. The brief allowed either.
  - Target 3's sketch says "Induct on `t` as `Turing.vhostEmitTM_runFrom` does; the visited-set
    clauses follow `Turing.vhostEmitTM_visitedByTapeHead_bank` …". The proof is
    `Lockstep.runFrom`/`.cut`/`.locate` plus `MultiTapeTM.mem_visitedByTapeHead_iff`, and has no
    induction of its own.
  - Fix as #133 did for target 1: an `**Implementation.**` paragraph for each (texts in (h)),
    plus the module's status text, its "Main results" line and the facade line.
- **F2 (public-facing text, cosmetic).**
  - Three new docstrings use the design label "R1" (`rd_slot`, and twice in `rd_pause_run`).
  - Four carry review narrative: "no new trace induction", "no second trajectory argument is
    needed", "the old trace" and "sharing the same test and dispatch proof". Eight more use
    "public" as review vocabulary ("the public phase lemma", …).
  - Eleven new privates have no docstring, among them the two witness machines `rd_callTM` and
    `rd_hostTM` (out/51).
  - The sketches are labelled "Proof sketch:", not `**Proof sketch.**`.
  - No campaign label, path or date was added (out/16). Rewordings are in (e).
- **F3 (records, minor).** REPORT and evidence are accurate in substance; four details:
  1. **The worker's final seal has no control.** Its one control (`inputMoveAction … rfl`) is
     from checkpoint 2, with no unsealed counterpart (`seal-control-cp2.log`). Its 17-name list
     includes `MultiTapeTM.outputSymbol`, which nothing reaches. My seal (rows 21–24) supplies
     the controls.
  2. **The bootstrap ran on the first-edit overlay**, base plus two 4-line status paragraphs:
     `InputDevice` warns at 439/507, not 435/499. Only that overlay's hash is shipped (out/37).
     This is consistent with REPORT; the paragraphs are gone from the head.
  3. **"35 new downloads, 1,002 unpacked"** means 967 archives were already in the cache tool's
     store on that host before the session's only fetch. REPORT does not say where they came
     from ((f)).
  4. The checkpoint zips cp2/cp3 are cited by hash only and are not in the inbox. Commit 1
     (`8fa8598e`) is cp2's state and is in the bundle.
- **O1 (an observation for the consumers' briefs, not a defect).** Two of the four exit states
  move again after the exit time:
  - The exit phase `.inr (.inr ())` falls to `rd_family`'s default, `rd_test`. So the read
    exits `(false, false)` (blank) and `(true, false)` keep running the test's return-leg table
    after `2ℓ + 5`: the input head and the ruler head move on the next step (out/30c, A1).
  - The move exit `(false, true)` and the read exit `(true, true)` are stationary.
  - The frozen statement says nothing after `t`, and a seam redirects at the exit. So this is
    harmless for seam consumers.
  - A consumer that needs a stationary live exit would need the exit phase mapped to a
    stationary leaf, a one-line change to `rd_family`. An example is the phase host's last-phase
    pattern: the user's ruling of 2026-10-22 (`02c8671e`) accepted the seam layout's F1 "with a
    last-phase lemma for the phase host to follow".

## Inputs

| Input | Identity | Evidence |
|---|---|---|
| Outer delivery `exchange/inbox/megafill-b-delivery.zip` | SHA-256 `14f6193f…14307e`; 6 members (the three item zips, `megafill-b-REPORT.md`, `recovery-verification.json`, `SHA256SUMS`), each byte-equal to `$S/inbox-megaB/zip/` | out/01, out/02 |
| Item zip `fill-b6-rulerdevice-cont1.zip` | SHA-256 `76f45501…0f38cf28`. This is the hash given, the session report's table, and its line in `zip/SHA256SUMS`. 93 members | out/01 |
| Extraction `$S/inbox-megaB/fill-b6-rulerdevice-cont1/` | every member byte-equal to the zip; no unsafe entry; CRC OK; no extra file | out/03 |
| `SHA256SUMS` | 92/92 OK; covers every member except itself | out/04 |
| Brief, dispatch copy `exchange/outbox/fills/b6-fill-rulerdevice-cont1.md` | `73e094a6…8ae4` (as given). It equals the base's `campaign/fills/b6/briefs/` copy (`526abe2c…`) with its three `@ANCESTOR@` set to the base. The records copy (`wt-hk`) and the tip's copy are the base blob | out/08 |
| Cover `megafill-B.md` and addendum v2.4 | dispatch copies `4e2e5a93…` and `42555a4f…`. Each equals its base copy (the cover after the same substitution). The worker's attachment log records the same five hashes, all "repository match: True" | out/08, `evidence/logs/attachment-verification.log` |
| Brief inputs | the 62-check probe, the 12-file population, the 95-module order list, the base sorry set (33 in 14) and the screen base (720/488/139,331), all read at the base | out/28, out/31, out/36, out/50 |
| Base `6cfee54474e3d954e3395f9d9eab5d025452a8dd` | a records commit; TCSlib tree `268944d6` = `2ff214c5`'s (#137's merge) | out/06 |
| Head `0f57ba49bf3ca8e5017dfed11ea010d723498284` | the bundle's only ref, fetched into `refs/review/f5-cont1` | out/05, out/06 |
| Snapshot `oleans-lg4c2` | `c60ed898`'s merged-tree replay (records `1d4fcf3e`: "lg4c2 13/13 at c60ed898"). The owned file's 19-module upstream closure has the same blobs at the base, at `c60ed898` and at the tip | out/39 |
| Campaign tip | `b7447492` (#139 and #143 merged after the base) when the review started. **It moved during the review** to `34af2e0f` (records only: `02c8671e`, the user's rulings; `34af2e0f`, gate 59's pack). The TCSlib tree is `2babcaec` at both, so the tip analysis at `b7447492` holds. Open Lean PRs: #144 (`ExhaustiveReplay`, docstrings) and **#145** (`lean/c1-seamlayout-fill`, the seam layout's landing, opened 16:56Z, as this review began) | out/38, out/44 |

Review worktrees, all detached under this folder, each with the `.lake/packages` link (checked
absent first):
- `wt-base` (the base), `wt-head` (the head);
- `wt-tip` (`b7447492` with the two patches `git apply`'d, uncommitted).

Lean ran only through `tools/leanelab.sh` (`scripts/elab.sh`), one elaboration at a time.
- Probe sources are in `wt-head/ReviewScratch/`, with copies in `probe/`; the hashes of every
  probe and script are in out/54.
- Scripts are in `scripts/`.
- No build or cache command was run.
- The delivered `executable-path.c` (SHA-256 `985924ad…4fba7`, the addendum's) was neither
  compiled nor run, and no delivered script was run.
- I read every delivered Lean file I elaborated (`ImportProbe.lean`) or compared by diff (the
  seal and axiom copies), and all of the head module.

## (a) Integrity and scope

| # | Check | Result | Evidence |
|---|---|---|---|
| 1 | Bundle | `verify` okay. One ref, `refs/heads/fill/b6-rulerdevice-cont1` = `0f57ba49…`, the hash in REPORT and in the session report. Its sole prerequisite is the base | out/05 |
| 2 | Commits | 2, linear, no merge; the first parent is the base. Author "Codex". Each touches only `Build/InputDevice.lean`: `8fa8598e` +273/−3, `0f57ba49` +503/−16; in all +759/−2 | out/06 |
| 3 | Patch series | the two patches applied in order at the base give the head tree `c4eff9db` and the head blob `f8339572`. Each equals `git format-patch --full-index` of its commit except the git-version trailer (`2.51.1`) | out/07, out/07b |
| 4 | Delivered source | = the head blob (SHA-256 `767e153e…`) | out/07 |
| 5 | Regions (`-U0`) | four hunks: <br>• home (a1): 240 lines inserted after the blank base line 414, before target 2's docstring; <br>• body (b1): base line 456 `  sorry` replaced by 31 lines; <br>• home (a2): 430 lines inserted after the blank base line 467, after `rulerHostCfg`; <br>• body (b2): base line 523 `  sorry` replaced by 58 lines. <br>Nothing outside them. Commit 1 also added the two region-(c) status paragraphs (base 434, 498); commit 2 removed them, so the head has none | out/10 |
| 6 | Reversal | base 1–414, 415–455, 457–467, 468–522 and 524–end are line-for-line head 1–414, 655–695, 727–737, 1168–1222 and 1281–end. Dropping the two homes and restoring the two `sorry`s gives the base byte for byte. So the module header, the imports, the frozen kit, target 1, `rulerHostCfg` and both target docstrings are untouched | out/14 |
| 7 | Freeze (`declfreeze.py … exists_rulerDeviceTM,exists_rulerHostTM`) | public 15 → 15, none added or removed, no `STATEMENT CHANGED`. Only the two targets have an "authorized body change". `exists_rulerTestTM` is unchanged. Private 9 → 41: 32 added, 0 removed, 0 changed | out/11, out/12 |
| 8 | Statements (`stmtcheck.py`) | of the base's 293 code lines, the only two missing are the two `  sorry` lines | out/13 |
| 9 | Hygiene (759 added lines; 684 code) | no `sorry`, `admit`, `axiom`, `set_option`, `open`, `section`/`namespace`/`end`, `variable`, `attribute`, `native_decide`, `decide` tactic, `instance`, `deriving`, macro or `#` command. <br>The four `unfold`s are the file's own (`rd_trace`, `rd_hostCost` ×3). <br>The 13 `decide` hits are terms (`decide (… = …)`: the tag and the verdict). <br>The 12 `change`s, 7 `show`s and 35 `rfl`s are covered by the seal (row 22) | out/15 |
| 10 | Names | 32 new privates, all `rd_`, in the two homes. No new public declaration. The 8 new public *constants* are auxiliaries: `_proof_`/`_simp_` of the two targets, and `rulerHostCfg.eq_1`/`.congr_simp`, generated by the new `simp only [rulerHostCfg]` | out/19, out/49 |
| 11 | Imports | unchanged: the five, `Build/Catalog` among them | out/14 |
| 12 | Widths, whitespace | added lines at most 96 characters; the file at most 100; no trailing whitespace, no tab, no double blank line; `git diff --check` clean | out/35 |
| 13 | Size | 525 → 1,282 lines; 15 public / 9 → 41 private (lint INFO) | out/34 |

**The 32 new privates** (head lines; out/19, out/51):
- **phase 2** (home a1, 15):
  - `rd_test_window` (418), `rd_test_return` (442): projections of `rd_run`;
  - `rd_answer` (453), `rd_direction` (458), `rd_leafMove` (462), `rd_leafAnswer` (465);
  - `rd_callLeaf` (469), `rd_Phase` (474), `rd_CallState` (475), `rd_family` (477),
    `rd_redirect` (481), `rd_callTM` (486);
  - `rd_call_run` (493), `rd_shift_move` (610), `rd_tagged_read` (642);
- **phase 3** (home a2, 17):
  - `rd_HostState` (739), `rd_resume` (742), `rd_pauseEmb` (747), `rd_slot` (761),
    `rd_slot_bank` (764);
  - `rd_hostAction` (770), `rd_hostTM` (776);
  - `rd_pause_run` (788), `rd_host_source_step` (871), `rd_next_tag` (924);
  - `rd_hostEnc` (949), `rd_hostCost` (955), `rd_hostCost_bounds` (962), `rd_hostFrame` (971),
    `rd_hostFrame_layout` (978);
  - `rd_host_block` (990), `rd_host_frames` (1123).

REPORT's two tables list exactly these, with accurate roles.

## (b) Elaboration and axioms

| # | Check | Result | Evidence |
|---|---|---|---|
| 14 | Base file, `oleans-lg4c2` | exit 0; `435:8` and `499:8` `declaration uses 'sorry'` only (= the pre-ship) | out/17 |
| 15 | Head file, `oleans-lg4c2` | exit 0, **no diagnostics**. A sanity copy with a planted error reports it, so elaboration is real | out/18, out/18b |
| 16 | Axioms: a copy of the module with `#print axioms` for all 56 declarations, an admission walk and a dependency walk | the three targets: `[propext, Classical.choice, Quot.sound]`. Direct `sorryAx` users in each closure: `[]`. All 56 are within the standard three (histogram 17 / 17 `propext, Quot.sound` / 6 `propext` / 16 none) | out/20, out/21 |
| 17 | Against the worker's 35 prints (`final-local.log`) | equal on all 35 names | out/48 |
| 18 | Other files' privates and equation lemmas reached | none. The only "eqn" hit, `Bool.eq_iff_iff`, is the tool's known name-pattern false positive | out/21 |
| 19 | TCSlib constants reached (all 56) | 82: 46 theorems (5 of them `_proof_` auxiliaries), 28 definitions (17 semireducible, non-projection, non-instance; 11 projections), 4 structures, 4 constructors. Two rfl-lemmas passed to `simp only`, `Action.apply_output` and `Action.apply_workTapePos`, leave no trace in the terms; both are public and in the issued probe | out/21-extlist-tcslib.txt, out/21b, out/23b |
| 20 | Used directly by the 32 new declarations | 66 TCSlib constants. Every theorem among them is in the worker's 148-name probe. Outside it are only structures, constructors, projections, the primitives in statements (`runFrom`, `step`, `Action.apply`, `Cfg.inputSymbol`, …) and two `_proof_1` auxiliaries | out/29b, out/29 |

## (c) Correctness, route and rule 10

I read the whole head file. Correctness rests on the kernel-checked proofs (rows 15–16). Below:
the construction, the brief's route, and the gate's instances run on the delivered machines.

**The call rows** (`rd_callTM := phaseHostTM rd_family ⟨.inl none, .inl ()⟩ rd_redirect`):
- **Phases** (`rd_Phase`):
  - `.inl op`, the test (`rd_test`, inherited and frozen);
  - `.inr (.inl (op, b))`, the leaf `rd_callLeaf op b`;
  - `.inr (.inr ())`, the exit.
- **Entries and exits.**
  - Read entry `⟨.inl none, .inl ()⟩`; move entry `m` `⟨.inl (some m), .inl ()⟩`.
  - Exits `⟨.inr (.inr ()), .inr p⟩`: `p = rd_answer v` for a read (`none ↦ (f, f)`,
    `some b ↦ (t, b)`), `(f, t)` for the move.
- **`rd_redirect`** dispatches the test's verdict `(b, true)` to the leaf `(op, b)`, and any leaf
  answer to the exit, each by one stationary step.
- **`rd_callLeaf`** is one `inputMoveAction`:
  - the move is `rd_leafMove op b`: `0` for a read, else `rd_direction m b`, which suppresses
    exactly `m = −1` on `b`;
  - the answer is `rd_leafAnswer`: `rd_answer (if b then none else inp)` for a read.

| Item | Status | Notes |
|---|---|---|
| Seam over the test; one-step leaves from the catalog's action | **as briefed** | the phase host, with `phaseHostTM_run` applied twice in `rd_call_run` (the test with `T = 2ℓ + 2`, the leaf with `T = 1`). The leaf's step is `step_of_inputMoveAction` with `rfl` on the file's own table. There is no private action or step lemma, and no catalog scan. Its stationary instance (`inputMoveAction 0`) is the read |
| Read | **as briefed** | blank on `yes`. On `no`, the native symbol under the head. `rd_tagged_read`: `inputCell z (ℓ + i) = inputCell y i` by `inputCell_of_drop`, the right blank included |
| Move | **as briefed** | right is native (clamped); stationary does nothing; left is suppressed on `yes` and native on `no`. `rd_shift_move` gives `(moveInputPos p (rd_direction m b)).val = ℓ + (moveInputPos i m).val` from `FinTM.moveInputPos_neg_val`, `moveInputPos_rightBoundary` and `_pos_of_ne_right`. Both clamps are covered: at `i = |y| + 1` the physical head is at `|z| + 1` |
| Time, cut, envelope | **as briefed** | exactly `2ℓ + 5 = (2ℓ + 2) + 1 + 1 + 1`, and `≤ 4(ℓ + 1)` since `ℓ ≥ 1`. No exit-phase state before `2ℓ + 5`: the two `phaseHostTM_run` windows carry other phase tags. The ruler head stays within `ℓ + 1`: `rd_test_window`'s `[−1, ℓ]`, and 0 during the leaf and dispatches. `readExit` is injective and avoids `moveExit` |
| Test reuse | **as briefed** | `rd_test_window` and `rd_test_return` are projections of `rd_run`'s three cases. There is no second trace induction (rule 7) |

**The host** (`rd_hostTM M` over `rd_HostState S := (S × Bool) ⊕ (S × rd_State)`, `inj q b :=
.inl (q, b)`):
- **Ordinary state `.inl (q, b)`.** The action is `rd_hostAction (M.tr q (if b then none else
  inp) bank) b`:
  - the input move is `rd_direction a.inputTape b`;
  - the bank's actions are the source's; the ruler gets `(none, 0)`; the output is the source's;
  - the successor is `a.state.map …`. A halting source action halts in the same step.
  - A live left move from `b = false` enters the paused test `rd_resume q' (.inl ()) = .inr (q',
    .inl ())`. Otherwise the tag becomes `false` after a right move and stays `b` otherwise
    (`rd_next_tag`).
- **Paused state `.inr (q, r)`.** The step is `embedEmitTM (rd_slot m) rd_test`'s, relabelled by
  `rd_resume q`. So the final verdict `(b', true)` lands directly in `.inl (q, b')`: no extra
  return step.

| Item | Status | Notes |
|---|---|---|
| A `Turing.Lockstep`, encoding `rulerHostCfg` with the tag `c.inputPos = 0` | **as briefed** | `rd_hostEnc`. Two instances share one block lemma (`rd_host_block`): exits `∅/∅`, which covers every source run, halted steps included, and exits `{none}/{none}`, which gives the cut |
| Cost | **as briefed** | `rd_hostCost`: `2ℓ + 3` exactly when the source action is live (`a.state.isSome`), the tag is clear and the move is `−1`; otherwise `1`, a halted source included. `1 ≤ cost ≤ 3(ℓ + 1)` gives `t ≤ t' ≤ 3(ℓ + 1)t` and `C = 3` |
| The test on the ruler tape by R1 | **as briefed** | `rd_pause_run`: `embedEmitCfg_mapState_eq` rebuilds the start. `MultiTapeTM.runFrom_mapState_of_agreeOn` transports `rd_run`, guarded by "not a verdict"; its `hagree` closes by `rfl` through the file's own `rd_hostTM`/`rd_pauseEmb`, sealed. The frames come from `embedEmitCfg_selected_*`, `_unselected`, `_output` and `rd_test_window`. There is no new transport proof |
| The source step | **as briefed** | `rd_host_source_step`: `step_of_some` twice, `Action.apply_state`/`_inputPos`/`_workTapes`/`_workTapePos`/`_output`, `Cfg.workTapeSymbols_eq`, and the tagged read. Neither `step` nor `Action.apply` is unfolded |
| Endpoint, cut, frames | **as briefed** | `L.runFrom`, `live.cut`, and `L.locate` inside `rd_host_frames`. That lemma splits the horizon nonrecursively (penultimate prefix, or the last block), so a post-step frame is at a source time `≤ t` despite `locate`'s closed endpoint. The ruler tape stays equal to `rt`, every cell. The ruler head stays in `[rp − 1, rp + ℓ]` |
| Space ledger | **as briefed** | bank: equality through `mem_visitedByTapeHead_iff` both ways (the frames give ⊆; the encoded endpoints at `time v` give ⊇). Ruler: ⊆ `[rp − 1, rp + ℓ]` from the frames. Z1's privates are not re-walked |
| `inj` a state map (gate 13, finding 2) | **as stated** | the statement asks no injectivity, and none is claimed |

**The gate's adversarial instances** (gate 13; gate 51, notes 8–9). The proofs are universal and
add no hypothesis: no nonempty payload, no `m > 0`, no liveness, no termination. I also ran the
delivered machines (out/30, out/30b, out/30c):
- **Hypotheses satisfiable.** `RulerAt 1 0 d i` holds at `ℓ = 1`, `z = [true]`, `y = []` for
  `i = 0` and `i = 1` (two `example`s), so the proved row applies.
- **Device, 15 runs**:
  - the read: at `i = 0` and at the empty payload's right blank `p = |z| + 1` it answers blank.
    With `y = [t, f]` it gives `y[0]`, `y[1]`, then blank at `i = |y| + 1`;
  - the moves: `−1` at `i = 0` is suppressed, `p` stays at `ℓ`. `+1` at `i = |y| + 1` clamps,
    including at `y = []`, where both right clamps coincide (D8, D13);
  - in all 15: the first exit at exactly `2ℓ + 5`; the ruler head displaced at most `ℓ`; the
    ruler tape (cells −10..20), the ruler head and the output restored.
- **Host, 9 runs.** At every source time `t` the block endpoint matches the encoded source:
  state with the correct tag, input head, bank cells and head, ruler, output; `t ≤ t' ≤ 3(ℓ+1)t`;
  the ruler head within `[rp − 1, rp + ℓ]` at every host time.
  - **Halting on a left move**, with the tag clear or set: cost 1, and the host halts at host
    time 1, with no pause (H1–H3).
  - **Two live left moves**: from `i = 1`, `ℓ = 1`, the costs are `[5, 1, 1]` (one pause, then a
    suppressed move); from `i = 3`, `ℓ = 2`, `[7, 7, 1]` (H4, H5).
  - **The right clamp at `i = |y| + 1`**, with `y = []`: cost 1 per step, the tag stays clear
    (H6).
  - **Zero bank tapes** (H8), **`t = 0`**, and **an initially halted source** (H9: the host is
    halted at 0 and absorbed).
- **After the exit** (O1): A1 shows the drift of the blank read exit; A2 and A3 show stationary
  exits.

**Rule 10.**

| # | Check | Result | Evidence |
|---|---|---|---|
| 21 | Seal set | the 17 other-file semireducible definitions the module reaches (non-projection, non-instance): <br>• `Action.apply` (`@[simp]`), `Action.mapState`, `Cfg.init` (`@[simp]`), `Cfg.inputSymbol`, `Cfg.mapState`, `Cfg.workTapeSymbols`; <br>• `FinTM.bufferTape`, `MultiTapeTM.runFrom`, `.step`, `.visitedByTapeHead`; <br>• `embedEmitCfg`, `embedEmitTM`, `inputMoveAction`, `tapeAction`, `moveInputPos`, `phaseHostTM`; <br>• `pairEncode` (reached only by the inherited header lemmas). <br>The worker's 17 are the same, minus `pairEncode` (its seal starts after those lemmas), plus the unreached `outputSymbol` | out/23b, out/24 |
| 22 | Seal S2: head line 206 (the first `rd_` declaration) to `end Turing` in a section, the 17 names `local irreducible`, plus `attribute [-simp] Turing.Action.apply Turing.Cfg.init` | **the body has 0 errors, 0 warnings.** With 19 controls at the top and 19 at the end: exactly 38 errors, the 38 controls. Each control closes only by unfolding one sealed definition (`rfl`), or for `Action.apply`/`Cfg.init`, by `simp` | out/25-seal-F5SealS2 |
| 23 | Seal S1 (no simp erasure) | body 0 diagnostics; 34 control errors. The four `simp` controls pass, as expected without the erasure | out/25-seal-F5SealS1 |
| 24 | Controls unsealed | all 38 pass (0 diagnostics); sealed controls alone: all 38 fail | out/25-seal-ControlUnsealed, out/25-seal-Control |
| 25 | `rw`/`simp`/`simpa`/`dsimp`/`simp_all`/`unfold` arguments in the added code | 376 occurrences, 137 identifiers: <br>• 28 TCSlib **theorems** (the `Action.apply_*`, `Cfg.mapState_*`, `Cfg.workTapeSymbols_eq`, `FinTM.moveInputPos_neg_val`, `runFrom_*`, `step_of_some`/`_halt`, `embedEmitCfg_*`, `embedEmitTM_runFrom`, `moveInputPos_*`, `mem_visitedByTapeHead_iff`, `runFrom_mapState_of_agreeOn`); <br>• 20 own declarations; <br>• 47 locals; <br>• the rest core/Mathlib lemmas, including `abs_le`, `if_pos`, `if_neg`, `ne_eq` and the `reduceCtorEq` simproc. <br>**No other-file definition.** The 14 unrestricted calls (11 `simp`, 3 `simp_all`; out/15) close goals over own definitions, `Set`/`Finset`/`Finset.sum` facts and `SignType` constants; S2 shows that none needs an erased `@[simp]` def | out/22, out/26 |

**Rule 11.**
- No R3 row in the added lines or among the 82 reached constants.
- No other file's private is reached (the dependency walk), and no `_private` token is added.
- The eight lexical hits are false positives: prose words; `S`; and `Cfg.mapState_state` and
  `FinTM.moveInputPos_neg_val`, both public theorems (rows 19–20), which share a short name
  with privates elsewhere.
- Every new private is `rd_`.

Evidence: out/27.

## (d) Escalations and promotion candidates

**Escalations: none, and I agree.** No missing lemma was needed: every fact about another file's
definition comes through a published equation (rows 20, 25), and the seal confirms it.

**Import probes (check 5).**

| # | Probe | Result | Evidence |
|---|---|---|---|
| 26 | The brief's `B6F5C1ImportProbe` (62 checks), standalone against `oleans-lg4c2` | 0 errors, 0 warnings | out/28-F5IssuedProbe |
| 27 | The worker's extended probe `evidence/b6/ImportProbe.lean` (148 checks, the issued 62 first, verbatim; its names = `external-citations.txt`), standalone | 0 errors, 0 warnings; the output is contained verbatim in the worker's `import-probe-final.log` | out/28-F5WorkerProbe, out/29 |
| 28 | The 148 checks appended to a copy of the head module, so the targets checked are the proved ones | 0 errors, 0 warnings | out/28-F5InModuleProbe |
| 29 | Citations outside the probes | **Outside the 148:** no theorem cited by the new code. **Outside the issued 62:** 19 theorems, all public at the base and all in the 148: <br>• `Action.apply_workTapes`, `Cfg.ext`, `Cfg.workTapeSymbols_eq`, `FinTM.moveInputPos_neg_val`; <br>• `runFrom_of_halt`, `runFrom_succ_eq_step`, `runFrom_zero`, `step_of_halt`; <br>• `embedEmitCfg_mapState_eq`, `embedEmitCfg_output`, `embedEmitCfg_selected_pos`, `embedEmitCfg_selected_tape`, `embedEmitCfg_state`, `embedEmitCfg_unselected`; <br>• `moveInputPos_pos_of_ne_right`, `moveInputPos_rightBoundary`, `moveInputPos_zero`, plus two `_proof_1` auxiliaries. <br>The brief's prose names most of these ("the `moveInputPos` lemmas", the `embedEmitCfg_*` family). Unused issued names: the seams (`seamCompTM*`, `seamReleaseTM*`), `embedSilentTM*`, `embedEmitCfg_eq`, `embedEmitTM_frame`, Z1's `vhost*` (the pattern only), `outputSymbol_of_some` and four `Action.mapState_*` | out/29, out/29b |

**Promotion candidates** (REPORT's notes, and my assessment):
1. **A `Lockstep` frames corollary** (from `rd_host_frames`; the strongest): if every block's
   intermediate configurations satisfy a frame of the pre- or the post-step source
   configuration, then every target time up to the run's total cost satisfies the frame of
   some source time `≤ t`. It is generic over `Lockstep` and belongs beside `Lockstep.locate` in
   `Build/Contract/Basic`. The closed endpoint of `locate` makes it non-obvious, and F6 and U2-E
   compose this host.
2. **A "source step plus bounded pause" block contract** (`rd_host_block` with `rd_pause_run`):
   a host that relabels an embedded silent test by a resume map and lands directly in the next
   ordinary state. This is the brief's "host step plus a pause" lemma. It is useful to U2-E's
   H2-F composition, but its shape (one optional pause per step) should be fixed by that
   consumer's brief first.
3. **The tagged clamped-move translation** `rd_shift_move` (and `rd_next_tag`): physical
   `ℓ + i` against virtual `i` under both clamps. It is useful to any offset input device;
   low priority.
4. Already served: the leaf action. The delivery uses `inputMoveAction`, as decision 1(ii) of
   the first round ruled.

**What this unblocks.**
- **F6** (`Complexity.space_universal`, `SpaceComplexity/Hierarchy.lean:150`). Its docstring
  already cites `Turing.exists_rulerHostTM` and `exists_rulerTestTM`. Hierarchy does not import
  `Build/InputDevice` today. Adding that import adds exactly one module to its upstream, with no
  cycle (out/52), so F6's brief can authorize it.
- **U2-E** (`Turing.universalK`, `UniversalK.lean:582`). It already imports `Build/InputDevice`
  (out/44), and its docstring (576) names the host.
- No file at the tip cites the three targets in code; only docstrings mention them (out/45).

## (e) Duplication and lint

| # | Check | Result | Evidence |
|---|---|---|---|
| 30 | Screen v3 script | SHA-256 `f4feac91…f181`, the same at base, head, tip and in the main repo | out/33 |
| 31 | Before (base, the brief's 12-file population) | `720 declarations; 488 pairs; 139,331 chars` (149 s). Byte-equal to the recorded base `b6-fill-rulerdevice-cont1-screen-base.txt` (comments aside) and to the worker's `screen-before.txt` | out/31, out/50 |
| 32 | After (head) | `741 declarations; 489 pairs; 139,439 chars` (159 s). Byte-equal to the worker's `screen-final.txt` | out/32, out/53 |
| 33 | New pairs (`pairdiff.py`, by name, against the before screen and the recorded base) | **1 new, 0 gone**: `InputDevice.lean::exists_rulerTestTM reproduces rd_test_return: 108/136 = 79%`. <br>• It is in-file and below 90%, and it is the pair REPORT lists. <br>• The shared text is the endpoint projection `rw [rd_run … (2ℓ+2)]; simp only [rd_trace, if_neg …, rd_cfg, Nat.sub_zero, add_zero]`. Frozen target 1 performs it inline, and `rd_test_return` states it as a lemma for the new rows. The justification holds: target 1 is frozen, and no trace induction is repeated. <br>• Optionally, later, target 1's last bullet could cite `rd_test_return` and remove the pair. That touches a frozen proof, so it is the user's call. <br>• The accepted pair `rd_trace_step`/`rd_read_nat` (81%) is unchanged. **"New copies: none" holds** | out/53 |
| 34 | Cross-file pairs and the known hazards | **none.** No pair at the head has an `InputDevice` declaration on one side and another file on the other. None involves Z1's `vhostEmitTM_*` or its privates, `UniversalStartup`'s `universalInput_read`/`_move`, the unary marker, or `Build/Catalog`'s action lemmas (in the population) | out/53 |
| 35 | Discipline | both screens ran one at a time under `nice -n 10`, each only when `pgrep -f copy-text-screen-v3` found none. The after screen waited about 5 minutes for another copy-text screen to finish | `scripts/screens.sh`, out/31–32 `.status` |

| # | Check | Result | Evidence |
|---|---|---|---|
| 36 | Lint, `TuringMachine/Build` | base `0 FAIL, 30 WARN over 39 files`; head `0 FAIL, 31 WARN`. The new WARN is `InputDevice.lean 1282 lines > 1000`; size alone is no driver (ground rule 8). The head output is line-equal to the worker's `lint-final.log` | out/34 |
| 37 | Proof sketches (policy §3) | every new proof over 20 lines has a "Proof sketch": `rd_test_window` (22), `rd_call_run` (112), `rd_shift_move` (30), `rd_pause_run` (78), `rd_host_source_step` (49), `rd_next_tag` (24), `rd_host_block` (128), `rd_host_frames` (44), and both targets (their frozen sketches; F1) | out/51 |
| 38 | Docstrings | 21 of 32 new privates have one. Missing (F2): `rd_leafAnswer`, `rd_Phase`, `rd_CallState`, `rd_family`, `rd_redirect`, `rd_callTM`, `rd_slot_bank`, `rd_hostTM`, `rd_hostEnc`, `rd_hostCost_bounds`, `rd_hostFrame_layout`. Policy §2 leaves private docstrings to reviewer discretion | out/51 |
| 39 | Public-facing text | 44 added docstring lines: no campaign label (F5, B6, gate, brief, finding, checkpoint, phase), path or date. "R1" ×3, four narrative phrases and eight uses of "public" (F2) | out/16 |

**Suggested rewordings (F2; optional, docstring-only):**
- `rd_test_window`: "The test's frames and its two-sided head envelope along the whole sweep.
  **Proof sketch.** Each of the three legs of `rd_run`'s trace gives the clauses directly."
- `rd_test_return`: "The test's restored endpoint at time `2ℓ + 2`, read off `rd_run`."
- `rd_leafMove`: "The leaf's input move: none for a read (`op = none`), else the requested move,
  with a left move suppressed at the virtual boundary."
- `rd_slot`: "The test's one tape as the host's last tape."
- `rd_pause_run`: "A paused test runs on the last tape through the forwarding embedding and the
  guarded state transport, and its verdict resumes the source; the test's trace supplies every
  frame. **Proof sketch.** Rebuild the embedded start (`Turing.embedEmitCfg_mapState_eq`),
  transport `rd_run` along the resume map while no verdict is reached, and read off the frames."
- New one-liners:
  - `rd_callTM`: "The call rows' controller: the phase host over the boundary test, the
    one-step leaf and the exit phase."
  - `rd_hostTM`: "The ruler host: an ordinary step performs the source transition through the
    tag; a paused step runs the boundary test on the last tape."
  - `rd_hostEnc`: "The host's encoding of a source configuration, with the canonical tag."
- Optionally, "Proof sketch:" → `**Proof sketch.**` throughout.

## (f) Environment (addendum v2.4, Part 3; shared across the queue)

| Item | Recorded | Evidence |
|---|---|---|
| Preflight (05:10:08Z) | `nproc` 9; cgroup v2. `memory.max` 8,589,934,592. `anon` 100,847,616 + `kernel` 193,372,160 + `shmem` 0 = 294,219,776. **Headroom 8,295,714,816 B = 7.73 GiB ≥ 4.** `oom`/`oom_kill` 0/0; `max` 85,641 is reclaim, not a shortage (v2.1). Disk 23,909,351,424 B = 22.27 GiB ≥ 12 on `overlay`. The arithmetic checks. **PASS** | `evidence/logs/preflight.log`, `preflight-summary.json` |
| Disk before this item (06:15:31Z) | 17,553,752,064 B ≥ the 3 GiB floor (Part 3, item 4) | `logs/b6/disk-before-item.log` |
| Toolchain | Lean 4.25.0 failed with `failed to locate application`. The Part 2 shim (`985924ad…`, = the addendum's, source shipped, binary not) gave `Lean (version 4.25.0, … cdd38ac5…)`. `LEAN_SYSROOT`/`LAKE_HOME` point at the fresh archive; `LD_PRELOAD` is scoped to Lean/Lake | `lean-start.log`, `lean-shim-start.log`, `shared-summary.json` |
| Roots | 40, byte-equal to my extraction from the three order lists' union (95 modules, = `queue-order-union.txt`). F5's own list also imports 40 roots directly | out/46 |
| Cache | the narrowed fetch. Lake cloned the manifest's packages, compiled the cache executable (the `[n/20]` Lake jobs; v2.4's note) and fetched the ProofWidgets release. Then `Attempting to download 35 file(s)` → 35/35, `Decompressing 1002 file(s)`, `Completed successfully!`. No failure, no retry. Zero-size oleans: none. Cache probe exit 0 | `cache-get.log`, `package-verification.log`, `cache-probe.log` |
| Packages | 11 `PASS` (URL and revision = the manifest); the 4 doc packages `ABSENT` (v2.4's "each package present" reading) | `package-verification.log` |
| Bans | no `lake build`, no unfiltered `lake exe cache get` and no cache command line anywhere in the delivery's files. The 1,002 files (vs ~7,506 in full) show the fetch was narrowed | out/47 |
| Bootstrap and sweep | each 95/95 in the order list's exact order, exit 0, 0 errors, wall-time/RSS by `wait4` (`/usr/bin/time` absent) | out/36 |

**Environment note (for a v2.5, not a finding against the fill).** 1,002 − 35 = 967 archives
were already in the cache tool's local store when the queue's single fetch ran. That is the same
count that a 35-root v2.3 fetch downloads (967 files in G4 cont2's review), so the host's store
was most likely pre-populated by an earlier session. This is the cache tool's own hash-named
store, so nothing was copied by hand. Still, the
addendum forbids "another session's … object store" and does not say whether that store counts.
Suggestion: v2.5 should either allow it explicitly or ask the worker to log the store's file
count before the fetch.

**The sweep** (out/36, `scripts/sweep.py`; the worker's logs):
- **Bootstrap** (06:15–06:24Z):
  - 33 sorry warnings in 14 modules, name for name the base set
    `b6-fill-rulerdevice-cont1-base-sorries.txt`;
  - `InputDevice`'s two are at 439/507 (the first-edit overlay, F3.2);
  - max RSS 2,935,872 KiB; Σ wall 511.652 s.
- **Final** (06:49–06:58Z; `InputDevice` checked at 06:54:37, after the final commit at
  06:53:35):
  - 31 in 13: the base set minus exactly the two targets;
  - `InputDevice` has no diagnostic;
  - all 404 diagnostics outside `InputDevice` are identical to the bootstrap's (file, line,
    column, kind, text);
  - max RSS 2,944,700 KiB; Σ 539.971 s.
- These match REPORT and the session report.

## (g) Landability

- **The owned file is unchanged from the base to the tip.** Its blob `83e1e66a` is the same at
  both, and no commit in `6cfee544..b7447492` touches it (out/38). The two patches apply in
  order at `b7447492` and give the head blob `f8339572` (out/40).
- **Upstream.** The 19-module upstream closure is the same at the head and at the tip, and all
  19 blobs are unchanged from the base to the tip and to `c60ed898` (`oleans-lg4c2`'s tree)
  (out/39). The tip's TCSlib changes since the base, `Build/StepClock` (#139) and
  `Build/ZoneRebalance` (#143), are not upstream.
- **Elaboration at the tip.** `wt-tip` against `oleans-lg4c2`: exit 0, no diagnostics (out/41).
  The module source and its upstream oleans are byte-identical to the head run's, so the axiom,
  seal and probe results carry over unchanged.
- **Replay closure** (downstream of `Build/InputDevice` over the tip's imports, out/42):
  `Build/InputDevice`, `UniversalK`, `SelfUniversal`, the `TuringMachine` facade, 4 modules.
  `SpaceComplexity/Hierarchy` is **not** in it: it mentions the host only in docstrings and does
  not import the module (out/45, out/52). The root `TCSlib` is not listed.
- **The campaign's merged-tree replay** (out/43, `scripts/merged.sh`):
  - The files changed from `e9e97970` (`oleans-l132b`'s tree `20da2f4d`) to the tip are 11:
    `ClassNP`, `ExhaustiveReplay`, `NTimeHierarchy`, `WindowClock`, the facade, `BufferWords`,
    `InputDevice` (#133), `InputWindow`, `Rewind`, `StepClock` and `ZoneRebalance`.
  - Their downstream closure plus this landing is **16 modules** (listed in out/43). It is the
    same 16 with or without this landing, since `InputDevice` is already in it.
  - No snapshot of the tip's tree `2babcaec` is recorded. `oleans-lg4c2` lacks #137 and #139
    (out/43c), and gate 59's `lsl` (at `7cd01f84`) lacks #139 and #143.
- **Overlap with the other landings** (each closure from its own head's imports, out/44):

  | Landing | Changes | Its closure | Shared with this landing's 4 |
  |---|---|---|---|
  | U2-S (same megafill, `8e1aee0f`, not yet landed) | `UniversalK` (+ `import Build.SeamLayout`) | `UniversalK`, `SelfUniversal`, facade | **`UniversalK`, `SelfUniversal`, facade** |
  | #145 (`lean/c1-seamlayout-fill`, `126127b8`) | `Build/SeamLayout`, facade | `SeamLayout`, facade | facade |
  | #144 (`lean/c1-exhaustive-sketches`, `0beb75a3`) | `ExhaustiveReplay` (docstrings) | `ExhaustiveReplay`, `ClassNP`, `NTimeHierarchy`, `Diagonalization` | none |

  - No other landing touches `Build/InputDevice`.
  - The landing adds only private declarations, so `UniversalK` and `SelfUniversal` see the same
    public API (statements frozen, row 7). U2-S's interaction is a re-replay, not a conflict:
    whichever of the two lands second re-elaborates `UniversalK`, `SelfUniversal` and the facade
    against the other's result.
  - After U2-S lands, `UniversalK` also imports `Build/SeamLayout`, so #145's closure grows to
    include it.
  - The order is free.
- **Expected after landing:** `Build/InputDevice` has 0 sorry warnings (2 → 0). The 95-module
  order list goes 33 → 31 (out/36). No other module's warnings change.

## (h) Recommendation

**Not yet clear to merge**: the landing PR has not been opened, replayed or gated. It is clear
once that PR's replay passes and its gate is recorded.

**Land (full): yes**, by a maintainer PR into `complexity/arora-barak-ch3-4` (the campaign
branch, not a stacked branch).

**Commits.** Cherry-pick, or squash, `8fa8598e..0f57ba49` from `refs/review/f5-cont1`
(prerequisite `6cfee544`). The series touches only the owned file, which is unchanged at the
tip. The subjects are public-facing already. They carry no session trailer; the author is
"Codex".

**Maintainer edits, docstring-only, in the same PR:**
1. **Module status** (`Build/InputDevice.lean` 45–47):

   > **Status.** Everything here is proved: the devices' correctness facts, the restoring
   > boundary test `Turing.exists_rulerTestTM`, the call rows `Turing.exists_rulerDeviceTM` and
   > the ruler host `Turing.exists_rulerHostTM`.

   "Main results" (65–66): "… — the call rows and the host (proved)."
2. **The facade** (`TuringMachine.lean` 226–228, in the tip's `Build/Rewind` style):

   > * `Build/InputDevice` — host H5: the input-device interface, the native device, and the
   >   bounded-prefix ruler device with its boundary test, call rows and host. Proved.

3. **F1, target 2**: append after its sketch, before ` -/`:

   > **Implementation.** One phase host (`Turing.phaseHostTM_run`) runs the boundary test, a
   > one-step leaf built from `Turing.inputMoveAction` (stationary for a read; for a move the
   > clamped move, with a left move suppressed on `yes`), and a final dispatch. Both rows take
   > exactly `2ℓ + 5` steps, so `C = 4`; they are one argument with the operation as a parameter.

   Optionally, also replace "Rows are joined by R2 seams; the dispatch steps add a constant." by
   "The phases are joined by the phase host; the dispatch steps add a constant." That edits
   frozen sketch text, so it is the user's call.
4. **F1, target 3**: append:

   > **Implementation.** The host is a `Turing.Lockstep` over `Turing.rulerHostCfg` with the tag
   > `c.inputPos = 0`. A block costs one step, or `2ℓ + 3` after a live left move from a cleared
   > tag: the test runs on the last tape through `Turing.embedEmitTM` and the guarded state
   > transport, and its verdict resumes the source directly. Hence `C = 3`. The endpoint, the
   > cut and the frames come from `Turing.Lockstep.runFrom`, `.cut` and `.locate`, and the
   > bank's visited sets are equal by `Turing.MultiTapeTM.mem_visitedByTapeHead_iff`.

5. **Optional (F2)**: the rewordings and one-liners in (e).

Line widths stay ≤ 100 characters. Then re-elaborate the module (expect 0 diagnostics), re-lint,
and re-run the v3 screen (docstring-only edits; expect the same pair set, or note the
difference).

**Replay:** the 4-module closure (`Build/InputDevice`, `UniversalK`, `SelfUniversal`, the
facade) into a snapshot of the tip, if the maintainer has one. Otherwise, the campaign's
16-module merged-tree replay from a copy of `oleans-l132b` (out/43). The replay worktree needs
the `.lake/packages` link. Expected: 0 failures, `Build/InputDevice` and the facade at 0 sorry
warnings.

**Review table for the PR body:**
- integrity: 92/92 sums, bundle, 2 commits, series = bundle = file;
- scope: four hunks in regions (a)/(b); statements and docstrings byte-identical; 32 `rd_`
  privates; imports unchanged;
- elaboration at the base and at the tip: 0 diagnostics;
- axioms: the standard three, no `sorryAx`;
- seal S2: 17 definitions plus the simp erasure, 38 controls;
- probes 62/62 and 148/148, also in-module;
- the gate's instances run (24);
- screen 720 → 741 declarations, 488 → 489 pairs, 1 new pair (in-file, 79%), 0 cross-file;
- lint 0 FAIL;
- sweep 95/95, 33 → 31.

**Decisions for the user:**
1. **F1: how to synchronize the frozen sketches.** Recommended: add the two
   `**Implementation.**` paragraphs (as for target 1 at #133) and leave the sketches. Or also
   correct target 2's "R2 seams" sentence.
2. **F2: the optional docstring rewordings**, in this PR or in the deferred public-facing pass.
3. **O1: should the read exits be stationary?** Not needed for seam consumers. If F6 or U2-E
   will treat the device's exits as live anchors, say so in their briefs, or ask for a
   stationary exit phase in a follow-up.
4. **Promotion** (the maintainer's window): the `Lockstep` frames corollary first; the
   "step plus bounded pause" block once U2-E's brief fixes its shape.
5. **The environment note** for addendum v2.5: the cache tool's pre-populated local store.
