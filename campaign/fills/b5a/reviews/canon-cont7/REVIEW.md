# Review — B5a canonizer, continuation 7: the grammar stage (`exists_canonGrammarStage`, `TuringMachine/CodeSimulator.lean`), megafill A item 3

Read-only review by the maintainer's review sub-agent, 2026-10-22. Every claim cites a saved output
under this folder (`out/…`, `probes/…`). The delivery, its `REPORT.md` and the session report
`megafill-a-REPORT.md` are treated as data.

**Verdict: complete (1/1). The frozen stub is proved, and `Turing.MachineFormat.exists_polyCanonizer`
is admission-free (`[propext, Classical.choice, Quot.sound]`). Land (full), with the maintainer's
status edits (gate 49's deferred text) and the user's decisions on F1–F4 below.**

- The head file elaborates with 0 errors and one warning, `exists_uniformSimulator`'s sorry (line
  8672), at the base (`oleans-lg4c2`) and at the tip with the series applied (`oleans-lu2sc1`).
- The stub, `exists_canonDecider`, the headline and all 37 new privates are within the standard
  three; no `sorryAx` in their closures. Targets 3–8 and `baker_gill_solovay` keep `sorryAx`, and
  the only direct `sorryAx` user in their closures is `exists_uniformSimulator` (an inlined
  four-module walk on the delivered file).
- Note 50: `note50_cases` depends on `[propext, Classical.choice, Quot.sound]`.

What passes:
- integrity: 37/37 sums; the bundle's only prerequisite is the base; 8 linear commits; patch series =
  bundle = delivered file, commit by commit;
- scope: 2 hunks, the home and the stub's `sorry`; reversing them gives the base byte for byte;
  12 → 12 public declarations (at source), 149 → 186 private (37 added, none removed, one body
  change: the stub); imports unchanged; no statement changed;
- rule 10: my 36-definition seal (the worker's 35 plus `inputMoveAction`), with 74 `rfl` controls
  that all fail sealed and all close unsealed, leaves the body clean; the worker's seal and control
  reproduce. No TCSlib definition is passed to `rw`/`simp`, and there is no `unfold`. One core
  definition is (`Bool.toNat`, F2);
- rule 11: `canonPreserveInstall` byte-identical; no R3 row cited anew;
- probes: the 224-check probe extended by the 29 further public names the proofs cite (253, 0 errors,
  at the base and on the delivered module), cont3's 118, `B5aContPreShip`, note 50; the two
  statements probes at the tip (stand-in, see (d));
- the v3 screen: 2,419 → 2,455 declarations, 2,633 → 2,692 pairs; my after-screen is byte-equal to the
  worker's. 59 new pairs, all in-file, none cross-file, none with a known hazard. Four are ≥ 90% (F3);
- lint: 0 FAIL, the base's 63 WARN over 82 files and 1 WARN over 5 files; widths ≤ 100;
- the sweep: the 118-module census by name is 37 = the base's 38 minus the stub.

Findings (none blocks landing):
- **F1 (route, minor; decision: accept).** The prescribed generic link `canonCounterRepeat` (brief
  step 1) is not used anywhere. Both loops are composed instead from `canonRepeat_orbit` and the
  public done/escape contracts: the link exposes neither the per-round chain nor a silence clause,
  and its bound grows with `n`. It is now dead code. REPORT's checkpoint 1–2 text says otherwise.
- **F2 (rule 10, minor).** `simp [Bool.toNat]` (twice) unfolds core's `Bool.toNat`. It creates the
  module's only new public constant, `Bool.toNat.eq_1`. A verified two-line fix exists.
- **F3 (duplication, minor; decision).** Four new in-file pairs are ≥ 90%:
  - the two cut legs, 97% each way;
  - `canonStageLeg4`/`Leg5` → `Leg1`, 94% and 91%.

  The brief's 90% rule binds only for the known hazards, so these are not violations. But two of
  REPORT's justifications are wrong, and "new copies: none" is not accurate.
- **F4 (docstrings, minor; landing edit or deferral).**
  - 13 new proofs of more than 20 lines have no "Proof sketch" (policy §3);
  - "checkpoint N" labels appear in four public-facing docstrings;
  - one docstring states the F1 claim, which is no longer true.
- **F5 (route, note; accept).** One further private machine, the never-executed parking phase
  `canonStageHaltTM` ("a further leaf is an escalation").
- **F6 (records, minor).** REPORT inaccuracies: the file size, the lint and own-check revisions, the
  bootstrap range, the citation inventory and its probe, the promotion candidates and the checkpoint
  zips (list below).
- **F7 (environment, minor).** The shared preflight and cache logs are not in item 3's zip, and no
  per-module memory is logged. The numbers check out against item 1's logs. The overlapping-screen
  deviation is disclosed and had no effect.
- **F8 (status text, landing edit).** Gate 49's deferred text rides this landing. The module header
  and the headline's docstring are drafted and checked (`out/50-landing-edits.diff`). `Codes2Tape`'s
  and `EXPCOM`'s appendices become wrong at this landing.

## Inputs

| Input | Identity | Evidence |
|---|---|---|
| Zip `exchange/inbox/fill-b5a-canon-cont7.zip` | SHA-256 `7fd5aa40…c9e2c` (as given and as the session report says); copied to `delivery/`, extracted to `delivery/x/` (41 entries) | out/sha256sums-check.txt |
| `SHA256SUMS` | 37/37 OK; covers every member except itself | out/sha256sums-check.txt |
| Brief `campaign/fills/b5a/briefs/b5a-fill-canon-cont7.md`, cover `campaign/fills/megafill/briefs/megafill-A.md` | read at the issue commit `6cfee544…` (with their `@ANCESTOR@` placeholders) | — |
| Base `6cfee54474e3d954e3395f9d9eab5d025452a8dd` | TCSlib tree `268944d6` = `2ff214c5`'s (#137's merge); owned file blob `a66e63c3` (= the tip's) | out/03 |
| Head `7e6829dc57a6fe8547d71b6cf379163c70278661` | the bundle's only ref (`HEAD`, not a branch name); fetched into `refs/review/b5a-canon-cont7` (as earlier reviews did) | out/01, out/02 |
| Snapshots | `oleans-lg4c2` (base) and `oleans-lu2sc1` (tip). CodeSimulator's upstream closure is **28 modules, without `Build/InputWindow`**. All 28 are blob-equal at the base, `c60ed898` (`lg4c2`'s tree) and the tip, and their oleans are byte-identical in both snapshots. So both snapshots are exact for the owned file, and #137's `InputWindow` change does not reach it | out/05-up-*.txt, out/05b |
| Campaign tip | `97299639` (= `$S/wt-hk`); open PRs #147 (`28150fc1`) and #149 (`3d0f80b5`) read from `origin/` | out/41 |

Review worktrees (detached under this folder, each with the `.lake/packages` link, checked absent first):
- `wt-base` (the base) and `wt-head` (the head);
- `wt-patch` (the base with the 8 patches `git apply`'d);
- `wt-tip` (`97299639` with the 8 patches applied, uncommitted).

Scratch Lean files are in each worktree's `ReviewScratch/`, with copies in `probes/`. Lean ran only
through `tools/leanelab.sh` (`scripts/elab.sh`), one elaboration at a time; there was no build or
cache command. Python that read delivered data ran with `python3 -I`, from `scripts/`. No delivered
script was run.

The screen ran once, at the head, under the lock and `nice -n 10`, for 5,305 s.
- A before-screen was queued behind it. After the session restart (coordinator: "do not start
  another screen") I disabled it by replacing `scripts/screen.sh` with a no-op by rename. The running
  screen kept its open copy (`screen.sh.as-run`).
- So the queued run never started (`out/22-screen-before.status`). The lock was released by the
  running screen's trap.

## Checks

### (a) Integrity and scope

| # | Check | Result | Evidence |
|---|---|---|---|
| 1 | Bundle | `verify` okay; one ref `HEAD` = `7e6829dc`; sole prerequisite the base | out/01 |
| 2 | Commits | 8, linear, no merges, first parent the base. Each touches only `CodeSimulator.lean`; in all +3,095/−1. Author `B5a fill agent <fill-agent@campaign>`. Times 11:18–19:39Z, inside item 3's window (branch 10:58:17Z) | out/02 |
| 3 | Patch series | each patch equals `git format-patch` of its commit (up to `index` lines and the `2.43.0` trailer). Applied cumulatively at the base, each gives its commit's blob. The final blob is `3acc87c1` | out/04, out/04b |
| 4 | Delivered file | = the head blob (SHA-256 `78c1df1d…`); 8,684 lines | out/03 |
| 5 | Regions | 2 hunks: 2,624 lines inserted after the blank base line 4952 (home (a), head 4953–7576), and base line 4980 `  sorry` → 471 lines (head 7604–8074). Reversing both gives the base byte for byte, and the comment-stripped code is identical. So the stub's docstring and statement, the headline's docstring, `exists_canonDecider`, cont6's lemmas, the D4 section and H1's region are untouched | out/06, out/06b, out/06c |
| 6 | Freeze (`declfreeze.py … exists_canonGrammarStage`) | public 12 → 12 (at source), none added or removed, no `STATEMENT CHANGED`. Private 149 → 186: 37 added, 0 removed, 1 changed (the stub's body) | out/07 |
| 7 | Private statements (`privstmt.py`), `stmtcheck.py` | `STATEMENT CHANGED: []`. `stmtcheck`: 0 base code lines missing, after dropping the stub's bare `sorry` (the greedy matcher otherwise pairs it with H1's `sorry`) | out/08, out/06c |
| 8 | Statement history along the series | only the three disclosed checkpoint lemmas (51d6bbc8) and `canonStageInc_value` (7e6829dc, the same proposition restated as a recursion) change statement; the seal-hardening commit is proof-only (7 bodies) | out/29 |
| 9 | Public constants at the tip (workflow §4) | the module's environment, base vs head: one new public constant, **`Bool.toNat.eq_1`**, an equation lemma of core's `Bool.toNat` realized by `simp [Bool.toNat]` (F2). No derived instance (the four instance builders are `private def`s). No other auxiliary. The upstream oleans are byte-equal in both snapshots, so the census holds at the tip | out/15 |
| 10 | Hygiene (owned region, code only) | no `sorry`, `admit`, `axiom`, `set_option`, `open`, `section`, `variable`, `attribute`, `instance`, `deriving`, `unfold`, `delta`, `native_decide` or `#` command. 14 `decide`s, all `(n : ℕ) ≠ m` on literals. Widest line 100; the file's one 102-character line (1145) is the base's; no trailing whitespace or tab. Three double blank lines (6321, 7003, 7576; cosmetic) | out/27 |
| 11 | Imports | unchanged | out/06b |
| 12 | Size | 5,590 → 8,684 lines; 12 public / 186 private (lint INFO) | out/24 |

**The 37 new privates** (head lines, out/13):
- checkpoint 1: `canonStageSkip_suffix` (4954), `canonStageSuffix_drop` (4969),
  `canonStageRoundSpec` (4982);
- checkpoint 2: `canonStageBuffer_none` (5053), `canonStageInnerSpec` (5068);
- checkpoint 3: `canonStageBlock_consumes` (5673), `canonStageOuterSpec` (5698);
- checkpoint 4:
  - definitions: `canonStageHaltTM` (6164), `canonStagePh` with `_fintype`/`_deceq` (6192–6219),
    `canonStageFamily`, `canonStageRed`, `canonStageFr`, `canonStageBank` (6235–6286);
  - lemmas: `canonStageInc_value`, `canonStagePad_value` (6169, 6185), `canonStageBank_fields`
    (6295), `canonStageCut_leg` (6324), `canonStageLeg0`–`Leg6` (6345–6901),
    `canonStageFrontSpec` (7015);
- checkpoint 5: `canonGramPh` with `_fintype`/`_deceq`, `canonGramFamily`, `canonGramRed`,
  `canonGramG` (7446–7505), `canonGramCut_leg`, `canonGramFin_suffix`, `canonGramMapComp`,
  `canonGramLedger` (7514–7559).

### (b) Elaboration and axioms

| # | Check | Result | Evidence |
|---|---|---|---|
| 13 | Base file, `oleans-lg4c2` | exit 0; sorry at 4965 and 5578 (= the pre-ship) | out/09 |
| 14 | Head file, `oleans-lg4c2` | exit 0; **only** `8672:8` (`exists_uniformSimulator`) | out/10 |
| 15 | Head file applied to the tip, `oleans-lu2sc1` | exit 0; only `8672:8` | out/11, out/12 |
| 16 | Axioms (an in-module copy: the 37 new privates, the stub, `exists_canonDecider`, the headline, `exists_uniformSimulator`) | all within the standard three except `exists_uniformSimulator` (its own `sorryAx`). Direct `sorryAx` users in the closures of the headline, the decider, the stub and every new private: **none** | out/14 |
| 17 | Against the worker's logs | every common print equal to cp2, cp3, cp5 and the final log. cp1/cp4 show the headline with `sorryAx` (the stub was still open then). cp1–cp4 were printed at earlier commits; mine are at the head | out/14c |
| 18 | Targets 3–8 and `baker_gill_solovay` on the delivered file (CodeSimulator + Codes2Tape + EXPCOM + Relativization inlined, each body in its own section; none of their 20 remaining imports is downstream; `oleans-lu2sc1`) | 0 errors. The headline is standard. The seven others carry `sorryAx`, and **the only direct user in each closure is `exists_uniformSimulator`** | out/28, probes/C7InlineTargets.lean |
| 19 | Other files' privates / equation lemmas reached by the new code | none. One reused auxiliary from this file, `canonUnaryFamily._proof_1 : NeZero (1 + 1)`, is shared by Lean's auxiliary-proof cache with `canonStageLeg2` and `canonStageRed` (benign) | out/14, out/26d |

### (c) Route, rule 10 and rule 11

The stub's statement is frozen and the proof is kernel-checked (rows 14–18), so correctness rests on
the checker. I read the statements of all 37 privates and the assembly. The construction:
- `canonStageRoundSpec` takes `exists_canonRecordRound` as the record round.
- `canonStageInnerSpec`: `canonReturnAdapter` around `seamCompTM W L`, where
  - `W` writes `(3^(k+1)).bits` on the inner counter;
  - `L := counterLoopTM N₀ anchor₀ (some escape₀)` iterates the record round.
- `canonStageOuterSpec`: `canonReturnAdapter` around the outer `counterLoopTM` over the inner block,
  counted by `u` (value `counterValue w + 1`). Its bound `(B₂ + 20)·(|x| + |w| + |u| + 1)²` does not
  depend on `n`.
- `canonStageFrontSpec`: a nine-phase `phaseHostTM` with seven framed rows (copy, skip, walk,
  write pad, skip, skip back, increment), then C1 embedded by `embedEmitTM` (bound = the header),
  then a park.
- The stub: a four-phase `phaseHostTM`:
  - the front;
  - `seamReleaseTM (embedEmitTM ι₃ P)`;
  - `canonSuffixTM`;
  - `canonStageHaltTM`.

  `canonGramLedger` gives the exponent `2·AF + 9·A₃ + 8`.

| Brief step | Status | Notes |
|---|---|---|
| 1. The record round on `canonCounterRepeat` | **deviated (F1)** | `r`, `valid`, `tail` and `B` are as prescribed (`B` = the round's own constant, C2's + 2). But `canonCounterRepeat` is never applied: 0 occurrences in the owned region, and no consumer anywhere in the file |
| 2. Inner block | **as briefed**, loop composed per F1 | `writeConstTM_run_ofCfg`; `seamCompTM_runFrom_left/right`; `counter_cfg_eq`; `canonReturnAdapter`. The loop section is `canonRepeat_orbit` + `counterLoopTM_run_done/_escape` |
| 3. Outer loop | **as briefed** (the increment option), loop composed per F1 | the padded copy plus `incrementTM_run_succ_ofCfg` (`incFixed_eq_none_iff_replicate`: no overflow); `canonSkipTable_eq`; the n-free count via `canonStageBlock_consumes` |
| 4. C1, then `canonSuffix_run` | **as briefed** | C1 embedded on the header bank; `canonSuffix_run` cited once; every failure dispatched to the park with the reject bit |
| 5. Ledger | **as briefed** | at most `|x| + 1` outer rounds; `counterOverhead_le`/`_le_of_le`; `length_pairEncode` |
| 6. Stub, note 50 | **done** | row 34 |
| Hosts | **as briefed**, plus F5 | public combinators only: no second host, seam, embedding transport or loop machine. Framed rows beyond the brief's four (`skipTM`, `walkTM`, `skipBackTM` `_run_ofCfg`) are public catalog rows |
| Amendments | **accept** | pass 1 strengthens this fill's own unlanded privates (no frozen statement); pass 2 is proof-only; pass 3 is an equivalent restatement (row 8) |

**Rule 10.**

| # | Check | Result | Evidence |
|---|---|---|---|
| 20 | Seal set | my walk: other-module constants in the types and values of the new declarations (and their auxiliaries), in the values of own definitions they reach, and in the types of own theorems they cite. 33 semireducible, non-projection, non-instance TCSlib definitions. The worker's 35 = mine − `inputMoveAction` + `Cfg.select`, `MultiTapeTM.step`, `codeReadUnary` (not reached). **Union: 36.** None is `@[simp]`-unfolded (so no `[-simp]` variant is needed). Abbrevs (`counterLoopOrbit`, the brief's permitted N3 case), projections and derived instances are not sealed | out/17a–c, probes/seal-names.txt |
| 21 | The worker's seal `Cp7Seal` and control `Cp7SealControl` (read; = the head + the attribute block) | seal: 0 errors (1 sorry warning). Control: exactly 1 error, on its `counterValue [true] = 1 := rfl` line | out/18-Cp7Seal.out, out/18-Cp7SealControl.out |
| 22 | My seal (`section C7Seal` over the home and the stub's proof, 36 `local irreducible`) | **0 errors**, 1 warning (H1's sorry, outside) | out/18-C7SealBody.out |
| 23 | Controls: one per sealed definition at the section's top and at its end, plus the worker's (74 in all) | 32 are `#seal_control` (`@f` against its delta-unfolded value at default transparency, which is what `rfl` checks). The four structurally recursive definitions (`incFixed`, `codeReadUnary`, `codeSkipRepeat`, `pairDecode`) get concrete `example … := rfl` controls. **Sealed: 74 errors, one on each control line, none in the body. Unsealed: 0 errors**, 64 "rfl closes" plus 10 clean `example`s | out/18-C7SealCtl.out, out/18-C7UnsealedCtl.out, out/18z |
| 24 | `rw`/`simp`/`simpa`/`dsimp`/`unfold` arguments (554 occurrences, 192 distinct heads, resolved by Lean in the region's namespace) | theorems only: published TCSlib field/run/contract lemmas, own privates, core/Mathlib lemmas and locals. **One definition: `Bool.toNat`** (core, `Init.Data.Bool`), in `simp [Bool.toNat]` at 6175 and 6181 (F2). No `unfold`/`delta`. The 18 non-`only` `simp`/`simpa` calls are covered by row 22 (no reached definition is `@[simp]`) | out/16, out/16b |
| 25 | `show`/`change` (85 lines) and `rfl` (126) | all pass under the 36-definition seal (row 22); the seal-hardening pass replaced the definitional reads by published equations, and `Cfg.select` no longer occurs in the region | out/16, out/22 |

**Rule 11.** `canonPreserveInstall` is byte-identical (base and head line 1255, 75 lines). No R3 row
appears in the added lines or among the direct citations, only the framed `_ofCfg` forms (out/32).

### (d) Escalations, probes and citations

| # | Check | Result | Evidence |
|---|---|---|---|
| 26 | Direct citations of the new code | 126 TCSlib constants (55 theorems, 49 definitions, 14 constructors, 8 inductives). **29 public theorems/definitions are outside the probe's 224**: `FinTM.bufferTape_eq/_nat/_nil/_of_neg`, `embedEmitCfg_state/_output/_inputPos/_unselected`, `seamCompTM_runFrom_left/_right`, `seamReleaseTM_runFrom_pos`, `counter_cfg_eq`, `counterOverhead_le`, `incFixed_*` (5), `pairEncode_eq_dbl`, `skipBackTM_run_ofCfg`, `walkTM_run_ofCfg`, and the definitions `copyTM`, `skipTM`, `walkTM`, `skipBackTM`, `writeConstTM`, `incrementTM`, `incFixed`, `dbl`. The worker ran no extended probe (rule 10's last bullet, F6) | out/26 |
| 27 | Extended probe (224 + 29 = 253 checks) | standalone at the base: 0 errors, 253 outputs. **So every citation is public at the base**. In-module on the delivered file: 0 errors | probes/C7P7ExtStandalone-base.out, probes/C7P7Head.out |
| 28 | cont3's import probe (118), `B5aContPreShip` (15), in-module on the delivered file | 0 errors each (the one H1 warning) | probes/C7P3Head.out, probes/C7PreShipHead.out |
| 29 | `B5aStatementsProbe`, `S1210StatementsProbe` | these import downstream modules, so they need the head's CodeSimulator olean, which no review tool writes. Run at the tip against `oleans-lu2sc1` as a stand-in: 0 errors each. S1210's census still detects its probe-local admission (182) | probes/*-tip.out |
| 30 | Why the stand-in is exact | the public statements are unchanged (rows 6–7), and the public environment differs only by `Bool.toNat.eq_1`. The worker's sweep ran the same probes on the delivered tree (0 errors) | out/15 |
| 31 | Escalations | none filed. Ground rule 4 applied to F1 ("a cited row that does not compose as the route says"); the worker worked around it inside the rules instead (cited privates and public contracts only) | — |
| 32 | Promotion candidates | REPORT lists none (the brief asks for each with its contract). For the maintainer's window: the adapter `canonReturnAdapter`; a strengthened link (F1's chain-and-silence form, which both new loops prove inline); the cut leg (F3); `canonGramMapComp` (a `Cfg.mapState` composition law); C1, C2 and the strip machine | — |

### (e) Duplication and lint

| # | Check | Result | Evidence |
|---|---|---|---|
| 33 | Screen inputs | `scripts/copy-text-screen-v3.py` blob `2a8df2dc` at base, head and tip; the population is cont4's 45 files (the same blob) | out/20 |
| 34 | Before | the worker's before log is **byte-equal** to the recorded base `2,419 / 2,633 / 824,240` | out/23 |
| 35 | After (head) | `2,455 declarations; 2,692 pairs; 885,426 chars`, **byte-equal to the worker's after log** | out/21, out/23 |
| 36 | New pairs (`pairdiff.py` vs the recorded base) | 59 new, 0 gone, **0 cross-file**. Two have a base declaration on one side: `canonStageBlock_consumes` ↔ `skipTable_consumes` (61%/50%). No pair with a known hazard (C1/C2 internals, `canonEmitVerdict`, the adapter, `canonCounterRepeat`, `codeSkipRepeat_iter`, StepBlockLoop, the R1 family) | out/23, out/23b |
| 37 | **Pairs ≥ 90%** | `canonGramCut_leg` → `canonStageCut_leg` 97%; `canonStageCut_leg` → `canonGramCut_leg` 97%; `canonStageLeg4` → `canonStageLeg1` 94%; `canonStageLeg5` → `canonStageLeg1` 91% (F3) | out/23 |
| 38 | Lint (`campaign_style_lint.py`) at the head | `TuringMachine` 0 FAIL, 63 WARN over 82 files; `Diagonalization` 0 FAIL, 1 WARN over 5 files; both = the base. The worker's TM log has the 8,689-line count of 7ef4a983 (F6) | out/24 |
| 39 | Proof sketches | 13 new proofs over 20 lines have no "Proof sketch" (F4). The stub keeps its frozen sketch | out/31 |
| 40 | Public-facing docstrings | no path or date; "checkpoint N" in four docstrings (4974, 5058–5059, 5688, 5694, 7004). "C1"/"C2" follow the base's own usage. The four instance builders have no docstring | out/19 |

### (f) Environment (addendum v2.4, Parts 1 and 3)

| Item | Recorded | Evidence |
|---|---|---|
| Shared logs in item 3's zip | **none** (Part 3 item 2: copy them into each item's zip); item 3's REPORT does not quote them (checklist item 1). They are in item 1's zip (`item1/preflight.log`, `cache-get.log`, `cache-probe.log`, `mathlib-roots.txt`), read there | out/35 |
| Preflight 05:11:11Z | 4 CPUs; cgroup v1 with no limit (`9223372036854771712`), so headroom = `MemAvailable` 15.24 GiB ≥ 4; `oom_kill` 0; 26,517,278,720 B = 24.70 GiB free ≥ 12 GiB, ext4. Post-toolchain 22.29 GiB ≥ 8. All as the session report says | out/35 |
| Cache | **41 roots, identical to my union of the three order lists' roots at the base** (118 modules). 1,023/1,023 downloaded, "Completed successfully!", no failure. The cache probe log records only a timing (no import, no exit status) | out/33a, out/33b, out/35 |
| Disk before item 3 | 21.8 GB per the session report; no log in item 3's zip | — |
| Bootstrap | 71 modules complete (1–71), module 72 started without an end marker; REPORT says "1–65". No per-module maximum memory (Part 1 item 6) | out/30, out/35 |
| Final sweep | 66–118, 53/53 OK, 19:43–19:51Z (after the head commit); **census by name: 37 = the base's 38 minus the stub** | out/30, out/30b |
| Overlapping screen (disclosed) | about 3 minutes of two screens (Part 3 item 5). No effect: the before log is byte-equal to the base, and the after log to mine | out/23, out/35 |
| Bans | no `lake build` or unfiltered `cache get` in the delivered logs | out/35 |

### (g) Note 50

| # | Check | Result | Evidence |
|---|---|---|---|
| 41 | The file | delivered `evidence/CanonNote50.lean.txt` byte-equal to the prescribed one; no `#eval`, `native_decide` or `IO` in code (the only hits are its docstring) | out/34 |
| 42 | Run on the delivered module (in-module) | 0 errors; `'note50_cases' depends on axioms: [propext, Classical.choice, Quot.sound]` (= the worker's) | probes/C7Note50Head.out |

## Findings

**F1 — route: the prescribed counter-loop link is bypassed (minor; decision: accept).**
- *Claim.* Brief step 1 says "Apply `canonCounterRepeat` at `exists_canonRecordRound`", and ground
  rule 7 says "never write a second … loop … lemma for something already … proved in your file". The
  delivered file never applies `canonCounterRepeat` (0 occurrences outside its own definition; it
  has no consumer left). Instead, both `canonStageInnerSpec` (5287–5455) and `canonStageOuterSpec`
  (5809–5985) compose their loops from `canonRepeat_orbit` and `counterLoopTM_run_done`/`_escape`,
  the ingredients of `canonCounterRepeat`'s own proof.
- *Why the link could not serve* (checked against its statement, base 4860–4953):
  1. On escape it gives only `0 < j ∧ (roundOrbit M τ c j).state = some escape`. It exposes neither
     the per-round chain (that round `j − 1` started valid) nor any output clause, so the stub's
     unconditional `output = []` cannot be derived from it.
  2. Its bound `n·(B + 4) + 2|w| + 2` grows with the counter value. For the outer loop `n + 1` can be
     about `2^|bits|`, and the n-free ledger needs the per-round consumption, which again needs the
     chain.

  The brief's own step 5 (at most `|x| + 1` records, independent of `n`) therefore cannot be met
  through step 1's link. Ground rule 4 called for an escalation, not a workaround.
- *Disclosure.* Partial: the amendment paragraph says the inner loop was "re-derived on
  `canonRepeat_orbit`". But REPORT's checkpoint 1 and 2 text still says the round is "the `spec`
  argument of `canonCounterRepeat`" and the loop is "`canonCounterRepeat` with
  `canonStageRoundSpec`'s spec". The docstring of `canonStageRoundSpec` repeats it ("This is the
  `spec` argument of the generic counter-loop link").
- *Duplication.* Argument-level only: no screen pair involves `canonCounterRepeat` (out/23).
- *Proposed resolution.* Accept the route: it uses only cited privates and public contracts, with no
  new loop machine, and it is kernel-checked. Correct the docstring (drafted, L4). In the
  maintainer's dedup window, either retire `canonCounterRepeat`, or restate it with the chain and a
  silence clause and re-point the two loop sections (about 300 lines).

**F2 — rule 10: a core definition passed to `simp` (minor).**
- *Claim.* `canonStageInc_value` (6169–6182) closes two cases with `simp [Bool.toNat]`, which unfolds
  `Bool.toNat` (core, `Init.Data.Bool`).
  - It is the only definition among the 192 argument heads (out/16b).
  - It realizes `Bool.toNat.eq_1` in CodeSimulator's environment: the module's only new public
    constant at the tip (workflow §4: an equation auxiliary, but of another module's declaration).
  - REPORT's "every … argument … is a published base lemma, a Mathlib lemma, one of this fill's own
    in-file privates, or a local" is therefore inaccurate.
  - No TCSlib definition is unfolded: the 36-definition seal with its 74 controls holds (rows
    20–23).
  - No name clash results: the downstream sweep and my inlined four-module file elaborate with it.
- *Proposed resolution.* Replace both lines by `simp only [Bool.toNat_true, Bool.toNat_false]`
  (`probes/boolfix.diff`). The fixed module elaborates with 0 errors and the one H1 warning
  (out/18y-boolfix.out), and the extra public constant disappears. Alternatively accept it as is,
  reading rule 10's "another file" as TCSlib only (decision 2).

**F3 — duplication: four in-file pairs ≥ 90%, and three justifications that do not hold (minor;
decision).**
- *Claim.*
  - The ≥ 90% pairs are the two cut legs (97% each way) and `canonStageLeg4`/`Leg5` →
    `canonStageLeg1` (94%, 91%), among 59 new in-file pairs. The brief's 90% factoring rule names
    only the known hazards, and none is involved. So the brief allows these pairs if they are listed,
    and REPORT lists them.
  - But REPORT's summary "**New copies: none** (no new pair reproduces a source at 90%+ outside the
    deliberately parallel in-file host legs)" sets an exception the brief does not have, and with
    pairs at 97% it is not accurate. Policy (**Duplication**): every instance must be human-approved.
- *The justifications that fail:*
  1. Cut legs: "a shared form would need a public abstraction over the family, which rule 9 (no new
     public declarations) forbids". A **private** lemma generic over `{n} (P : Fin n → Type)` and a
     parking index is allowed, and it would serve both `Fin 9` and `Fin 4`.
  2. `canonStageBlock_consumes` ↔ `skipTable_consumes` (61%): "the base lemma is cited (not
     re-proved) where it applies". `skipTable_consumes` is not cited; its per-record bound `ha`
     (6 lines) is re-proved verbatim, because it is a local `have` of a frozen private.
  3. The seven stage legs (51–94%): the per-leg split is the right fix for the monolith's memory
     blow-up, but it does not prevent a shared leg lemma parameterized by the row contract.
- *Proposed resolution.* Accept and record the families for the maintainer's window (the cut-leg
  lemma, the leg template, the per-record bound as its own private), or have them factored before
  landing (decision 3).

**F4 — docstrings and sketches (minor; a landing edit or a deferral).**
- *Claim.* Policy §3 ("every nontrivial formal proof", landing checklist item 4) is not met: there is
  no "Proof sketch" for `canonStageRoundSpec` (47 lines), `canonStageInnerSpec` (570),
  `canonStageBlock_consumes` (21), `canonStageOuterSpec` (437), `canonStageLeg0`–`Leg6` (65–94
  each), `canonStageFrontSpec` (389) and `canonGramLedger` (22).
  - Their docstrings state the contracts well. Inside the proofs there are few comments: five each in
    the inner and outer specs, one in the front, none in the seven legs (the stub's proof has 11).
  - Public-facing text: "checkpoint N" in four docstrings.
  - `canonStageRoundSpec`'s last sentence is F1's stale claim.
  - The four instance builders have no docstring (reviewer discretion).
  - There are three double blank lines.
- *Proposed resolution.* The label rewording and the stale sentence are drafted (L4, in
  `out/50-landing-edits.diff`; docstring-only, checked). For the 13 sketches: either the maintainer
  writes them in the landing PR from the contracts and REPORT, or a backlog item takes them to the
  docstring pass (decision 4).

**F5 — a further private machine (note; accept).** `canonStageHaltTM` (6164) is a one-transition
parking machine, used as the last phase of both hosts.
- The brief says "Leaves you may write: none is expected. A further leaf is an escalation", and
  REPORT lists the machine without flagging it.
- It is never executed: the contracts read its state only at the dispatch instant.
- `canonHaltTM` cannot serve, since it emits a bit and the stage must be silent.
- `canonReturnAdapter` avoided a park by reusing its source machine; that is possible here too, but
  would change the phase families.

Recommend accepting it.

**F6 — records (minor).** Where REPORT and the session report are inaccurate (out/36):
1. "8,696 lines; +3,106; 3,107 insertions": these are commit `213816e0`'s figures. The delivered file
   has 8,684 lines, +3,095/−1.
2. The lint log is commit `7ef4a983`'s (8,689 lines). There is no own-check log at the head
   (`cp5-owncheck` is `7ef4a983`'s, line 8677). My runs at the head fill both gaps, with the same
   results.
3. The bootstrap covers modules 1–71 plus a started 72, not "1–65". The session report's "sweep 66–118
   twice" matches only one log.
4. "The import probe's list covers them" is false: 29 cited public names are outside the 224, and no
   extended probe was run. Mine passes (row 27).
   - The inventory lists `skipTable_consumes` and `codeSkipRepeat_zero`/`_succ` as cited; none is.
5. The checkpoint 1–2 descriptions (F1). "All six checkpoints": five, plus note 50.
6. The seal has one control, with no unsealed counterpart; mine has 74 (row 23).
7. No promotion candidates are listed (row 32). The checkpoint zips cp1–cp5 are not in the inbox and
   are not named in item 3's REPORT.
8. "New copies: none" (F3).

**F7 — environment (minor; for the next dispatch).**
- Item 3's zip has no copy of the shared logs (preflight, roots, cache, cache probe; Part 3 item 2),
  and its REPORT does not quote them (Part 1 item 1, checklist item 1). There is no log of the
  pre-item disk check. The logs record no per-module maximum memory (Part 1 item 6).
- The numbers themselves are right: item 1's logs give 4 CPUs, 15.24 GiB headroom and 24.70 GiB free
  disk; the 41 roots equal my computation; 1,023/1,023 files were fetched.
- The disclosed overlapping-screen deviation broke Part 3 item 5 for about 3 minutes, without effect
  on any result.
- *Proposed resolution.* No action for this landing. For the next megafill's cover brief, require the
  shared logs in every item's zip and per-module memory (or `wait4` maxrss).

**F8 — the canonizer's status text (gate 49's deferral; a landing edit).**
- *Claim.* After this landing the module header (45–73: "partial. The two headline contracts retain
  their original admissions … Still open: the canonizer's grammar loop") is wrong.
  - So is the headline's docstring: "(spec, fill pending — batch B5a)" and seven "Fill appendix"
    paragraphs, the last saying the stage "remains explicitly open" and note 50 "pending".
  - Gate 49's resolution (#13) assigns the CodeSimulator text to this landing.
  - Also wrong after this landing: `Codes2Tape` (43–44, 58–59, 301, 317–320) and `EXPCOM` (72, 121,
    150–153, 661–663) say "modulo the two §12.11 contracts" and "both shared contracts remain
    admitted". Only `exists_uniformSimulator` remains.
- *Proposed resolution.* `out/50-landing-edits.diff` (`scripts/landing_edits.py`, every replacement
  asserted). It is docstring-only: the comment-stripped code is identical, no statement changes, and
  it elaborates at the tip with 0 errors and the one warning (out/50b, out/50c).
  - L1: the module header's current status. It drops the `audits/` paths and dates.
  - L2: the headline's docstring. The tag goes, and the seven appendices become one
    `**Implementation.**` paragraph, which records continuation 5's escalation as resolved by the
    fresh-anchor adapter.
  - L3: an `**Implementation.**` paragraph for the stub (the route taken).
  - L4: F4's labels and F1's stale sentence.

  Codes2Tape/EXPCOM: in this PR, or in the deferred docstring pass as gate 49 ruled (decision 5).

## Decisions for the user

1. **F1, the loop route.**
   - (a) Accept the re-derived loops (recommended).
   - (b) Ask for a continuation that re-points them to a strengthened `canonCounterRepeat`.

   Separately, `canonCounterRepeat` is now dead code:
   - (i) retire it in the dedup window;
   - (ii) restate it with the chain and silence clauses, and re-point both loops there;
   - (iii) leave it.
2. **F2.**
   - (a) Apply the verified two-line `Bool.toNat_true`/`Bool.toNat_false` fix as a maintainer
     commit in the landing PR (recommended; it removes the only new public constant).
   - (b) Accept it, reading rule 10's "another file" as TCSlib files.
3. **F3, duplication.**
   - (a) Accept the 59 in-file pairs, including the four ≥ 90%, as recorded debt with named families
     (the cut leg, the leg template, the per-record bound) for the maintainer's dedup window
     (recommended).
   - (b) Factor the cut legs (and optionally the legs) before landing.
4. **F4, sketches.**
   - (a) The maintainer adds the 13 sketches in the landing PR.
   - (b) Defer them to the public-facing docstring pass with a backlog item.

   In either case, apply L4.
5. **F8, the status text.** Approve the L1–L3 wording. Codes2Tape/EXPCOM:
   - (a) in this PR (docstring-only; both files are already in the replay closure);
   - (b) in the deferred pass.
6. **Ordering and history.**
   - Ordering against #149 (whose 324-module closure contains this landing's 10 modules), #147, and
     items 1–2 (see Landing).
   - Commit messages: keep the 8 worker commits (authorship preserved, per workflow §4's `git am -3`;
     their subjects carry campaign narrative such as "checkpoint", "seal hardening", "duplication
     governance"), or squash them.
7. **F5.** Accept the parking machine (recommended).
8. **F7.** Add "shared logs in every item zip" and "per-module memory" to the next megafill's cover
   brief.

## Landing

**Not yet clear to merge.** The landing PR is not open, its replay has not run, and its fill gate
is not recorded. It becomes clear once the PR targets the campaign branch (not stacked), its
merged-tree replay has passed and the gate is closed.

**Land (full): yes**, by a maintainer PR into `complexity/arora-barak-ch3-4`.
- **Commits.** Cherry-pick the 8 commits `0b7c99d6…7e6829dc`, or `git am -3` the 8 patches, onto the
  tip `97299639` (full hashes in out/43; from `refs/review/b5a-canon-cont7`; prerequisite `6cfee544`):
  - `0b7c99d63907e29632a00aea0393b84df6622eb7`
  - `a6c90c60e25d200b5d4f2041a2646b247ca527b3`
  - `aad5fbe8d78901a8f499ad6b2506a7bccde3acf9`
  - `4b8d053d90b3cd72c9649c5b147ad0203a2c45da`
  - `51d6bbc819329bbd54a6a4f6e465d03b6f613c1b`
  - `7ef4a98369d8a660d42e9a821cff5fdf9be7538a`
  - `213816e0ed4a12ee6905887916799892d1538725`
  - `7e6829dc57a6fe8547d71b6cf379163c70278661`

  They touch only the owned file, which is unchanged at the tip. The series applies there and gives
  the head blob `3acc87c1` (out/11). Link `.lake/packages` in the PR worktree.
- **Maintainer commits in the same PR:**
  - the status text L1–L3 (gate 49's deferral) and L4;
  - per the decisions, F2's fix, the sketches, and Codes2Tape/EXPCOM.

  Every draft is checked: 0 errors, widths ≤ 100, code unchanged (out/50*).
- **This landing's replay closure at the tip** (`mkdownmulti.py`, root excluded) is **10 modules**:
  - `TuringMachine/CodeSimulator`, `Diagonalization/EXPCOM`, `TuringMachine/NDCodeSimulator`,
    `Diagonalization/NTimeHierarchy`, `Diagonalization/Relativization`, `Diagonalization`,
    `TuringMachine/Codes2Tape`, `TuringMachine/UniversalK`, `TuringMachine/SelfUniversal`,
    `TuringMachine` (the facade).
  - Replay them into a copy of `oleans-lu2sc1`. It is exact for the tip, because it differs from the
    tip only in UniversalK/SelfUniversal, both of which are in the list.
  - Expected warnings:
    - CodeSimulator 1 (`exists_uniformSimulator`);
    - NDCodeSimulator 2 and NTimeHierarchy 2;
    - UniversalK 3, or 2 if #147 has merged;
    - the rest 0.
  - Expected order-list census: 37.
- **Overlaps** (no changed file in common with any of them; out/41, out/42):
  - **#147** (UniversalK, facade): its 3-module closure lies inside this one. Either order works.
    Whichever lands second replays on the merged tree. If #147 is first, this landing's 10 modules
    from a snapshot of #147's merged tree; if this is first, #147's 3 from this landing's
    snapshot.
  - **#149** (Deterministic, Finite, `Build/WindowRun`): its closure is 324 modules, and this
    landing's 10 lie inside it.
    - If #149 merges first: replay these 10 modules into a copy of #149's merged-tree snapshot
      (`lspapi`, if its tree is the merged tree at `3d0f80b5`).
    - If this lands first: #149's 324-module replay must be re-run on the merged tree.

    Recommended: land #149 first.
  - **Items 1 and 2 of megafill A** (`NDCodeSimulator`, closure 4; `NTimeHierarchy`, closure 2): both
    lie inside this landing's closure. Whichever of the three lands later replays its own closure
    from the latest merged-tree snapshot. Never compose snapshots.
- **After landing:**
  - `exists_polyCanonizer` and `note50_cases` are admission-free;
  - `exists_uniformMachineCode2`, `exists_uniformMachineCode`, the EXPCOM cluster and
    `baker_gill_solovay` reach `sorryAx` only through H1's `exists_uniformSimulator`;
  - CodeSimulator keeps that one admission.
- **Review table for the PR body:**
  - integrity: 37/37 sums, bundle, 8 commits, patches = bundle = file;
  - scope: 2 hunks, 37 privates, 12 → 12 public;
  - elaboration: base and tip, the one H1 warning;
  - axioms: standard for the headline, the stub and every new private; targets 3–8 and BGS through H1
    only;
  - seal: 36 definitions, 74 controls;
  - probes: 253/118/15 and note 50;
  - screen: 2,419 → 2,455 declarations, 2,633 → 2,692 pairs, 0 cross-file;
  - lint: 0 FAIL;
  - census: 38 → 37.
