# Review — C1, R continuation 2, the interpreter core (`Turing.exists_ndInterpreterCore`, `TuringMachine/NDCodeSimulator.lean`), megafill A item 1

Read-only review by the maintainer's review sub-agent, 2026-10-22. Every claim cites a saved
output under this folder (`out/NN-*`). The delivery, its REPORT.md and the session report
(`megafill-a-REPORT.md`) are treated as data.

**Verdict: complete (1/1), proved modulo exactly `Turing.exists_replayCanonizer` at the tip
(at the base also `Turing.exists_seamLayoutTM`). Rule 10 fails at six sites (F1), each closed by
a proof-only repair that this review drafted and checked sealed. Land, with that repair and
the status edits in (h).**

- The delivered file elaborates with 0 errors and exactly the replay canonizer's sorry warning
  (line 95). This holds at the base (`oleans-lg4c2`) and at the tip with the file applied
  (`oleans-lu2sc1`) (out/13, out/40).
- The target depends on `[propext, sorryAx, Classical.choice, Quot.sound]`. Its direct `sorryAx`
  users at the tip: **`[Turing.exists_replayCanonizer]` only**. At the base, the seam layout is
  one too. Against `lg4c2` the window copier is a third, because that snapshot's
  `Build/InputWindow` is the build from before #137's proof (out/15, out/16, out/17, out/36).
- The route is the brief's: a left-nested seam composite of twelve phases in the prescribed
  startup order. It uses the published `rewindTM_run_ofCfg` three times and `copyTM_run_ofCfg`,
  the window, the install, the layout and the hosted loop. The ledger
  `C = a + 43 + (CW + 2) + 50(L + 1) + 10` gives both clauses through `ic_time_ledger`. One
  piece deviates: the input-rewind leaf (F2).
- **The seal fails** (the worker ran none). With 46 other-file definitions locally irreducible,
  six sites in three declarations fail:
  - four `show`/`exact` steps in `ic_rewind_scan` and `ic_rewind_leaf_run` close only by
    unfolding `MultiTapeTM.runFrom`;
  - the target's verdict, `rw [if_pos hP, …]`, closes only by unfolding `CodeNDTM.toFinNDTM`
    (confirmed by a bisect).

  The repair (`out/21-repairs.diff`, 4 hunks, proof-only) elaborates with 0 errors. The repaired
  file passes the seal S1 and the stronger S2 (the seal plus the four `@[simp]` definitions
  erased), and every one of the 46 + 4 controls fails sealed and passes unsealed. Its axioms equal
  the delivered file's, print for print (out/19-seal-summary.txt, out/17c).

What passes:
- integrity:
  - 34/34 sums;
  - the bundle's only prerequisite is the base;
  - 19 linear commits;
  - `git am` of the 19 patches reproduces every commit's tree;
  - the delivered file is the head blob `7d1657b3`;
- scope:
  - 3 hunks, all in regions (b)–(c), plus the imports (a) as the first edit (= the overlay);
  - the target's statement and docstring are byte-identical;
  - the 20 overlay privates are verbatim, and there are 5 new `ic_` privates;
  - 3 → 3 public declarations;
- rule 11; the brief's 220-check probe (= the worker's) and a 238-check extended probe, 0
  errors each, at the base and at the tip;
- the v3 screen reproduces the worker's exactly: 460 → 465 declarations and 118 → 120 pairs.
  Both new pairs are disclosed. One is cross-file (F3);
- lint: 0 FAIL, and the one new WARN is the file size (2,419 lines);
- the worker's 118-module census (bootstrap + sweep + the owned module's final check): 38 → 37,
  the target only.

Findings:
- **F1 (rule 10, major; resolved by the review's repair).** Six definitional closures through
  other files' definitions. The brief forbids these ("no `rfl`, `exact`, `show` … step that closes
  only because another file's definition reduces"). The REPORT claims the inspection "found no
  definitional closure".
- **F2 (route/duplication, minor; decision).** The input rewind does not run "through
  `FinTM.rewind_heads`", as the route and ground rule 7 say. `ic_rewind_scan` re-proves the
  published `FinTM.rewind_scan`'s induction: 479/1,195 characters, 51% of `rewind_scan` on the v3
  metric. `Simulation` is outside the brief's screen population, so the screen could not see it.
  The REPORT does not disclose it.
- **F3 (duplication governance, minor; decision).** The new cross-file pair
  `ic_rewind_leaf_run`/`InputWindow::iw_one` (69%) breaches the brief's "no new cross-file pair".
  It is three lemma-name fragments (85 characters of a 124-character one-step lemma), the same
  kind as the base's already accepted `ic_verdictTM_run`/`iw_one` (67%). It is not a copy
  family.
- **F4 (records, minor).** Several REPORT statements are wrong or stale:
  - the size (1,866 lines claimed; the file has 2,419);
  - "all new citations are from the probe's list" (12 theorems and 4 definitions are outside it);
  - the shipped `SORRY-DIFF.txt`, which is not the census REPORT quotes;
  - a 2-print axiom log;
  - a stale "the stop is the budget";
  - one checkpoint zip instead of one per phase, and that one, cp4, is absent.
- **F5 (landing mechanics, minor).** Three commits are evidence-only. One (`d1a49114`) mixes the
  owned file with eleven files under a repository-root `evidence/`, among them two `.lean`
  probes and a nested bundle. Land by `git am -3 --include=<owned file>` of 16 patches; this was
  rehearsed onto the tip and gives the delivered blob.
- **F6 (environment, note).** Two disclosed process deviations:
  - the 80 non-upstream modules were first built by the final sweep, where Part 3 item 3.2 asks
    for a whole-list re-bootstrap;
  - a briefly duplicated sweep (`CfgRecord` SIGKILLed, then rerun).

  Neither affects any result.
- **F7 (docstrings, landing edit).** Two status lines still say "sorried". The frozen proof
  sketch installs before the window copy and omits the rewinds, the copy and the layout, so an
  optional `**Implementation.**` paragraph is drafted. All are checked.

## Inputs

| Input | Identity | Evidence |
|---|---|---|
| Zip `exchange/inbox/fill-c1-core-cont2.zip` | SHA-256 `4a2896a39cba455ef03997b8d5162c979569615f97f68a7087fe1feea159ce9b` (as given). 37 entries (35 files), each byte-equal to `delivery/x/`; CRC OK; no unsafe name | out/01, out/02 |
| `SHA256SUMS` | 34/34 OK; covers every file but itself | out/03 |
| Zip files vs the bundle | every log, REPORT and the source equal their `evidence/delivery/item1/` copies at the bundle head. `evidence/logs/item1-owned-final.log` (the owned module's final check) is in the bundle only | out/03c |
| Brief (dispatch copy `exchange/archive/fills/c1-fill-core-cont2.md`) | SHA-256 `0ae5cd62…def756` = the base's brief (`8252114c`) with `@ANCESTOR@` := the base = REPORT's hash | out/07 |
| Cover `megafill-A.md`, addendum v2.4 | base blobs `a1c41e6b`, `e3fd647d`. The cover is unchanged at the tip; the addendum is v2.5 there, and megafill A runs under v2.4 | out/07 |
| Brief inputs | overlay (`8d445ae6`), 220-check probe, 12-file population, 118-module order list, base sorries (38 in 17), screen base (460/118/43,576), pre-ship log: base = tip blobs | out/07 |
| Base `6cfee54474e3d954e3395f9d9eab5d025452a8dd` | ancestor of the tip. The owned file is unchanged base → tip (`2d41f8f4`) | out/36c |
| Head `189e4675d98727ae3306aab2c087e106acdb7847` | the bundle's only ref (`HEAD`), fetched into a scratch bare repository with alternates (`bundlerepo/`), not into the repository | out/04 |
| Campaign tip `97299639f3a7b4e51f4f94127647cbb915158393` | `wt-hk`. TCSlib changes since the base: ExhaustiveReplay, the facade, InputDevice, SeamLayout, StepClock, ZoneRebalance. Of these only SeamLayout is upstream, and `exists_seamLayoutTM`'s statement is unchanged | out/36c |
| Snapshots | `oleans-lg4c2` (tree `c60ed898`): equal to the base on the head's 37 upstream modules **except `Build/InputWindow`**, which is the statement-identical build from before #137's proof (`exists_inputWindowCopyTM` sorried there; only its proof differs). `oleans-lu2sc1` (tree `28150fc1`): equal to the tip on all 38 upstream modules (the tip adds `BufferWords` through SeamLayout); it differs from the tip only in `UniversalK` and the facade (#147) | out/36, out/36b |

**Review worktrees** (detached, under this folder, each with the `.lake/packages` link, checked
absent first; out/00):
- `wt-base` (the base);
- `wt-head` (the base + the delivered file);
- `wt-tip` (the tip + the delivered file);
- `wt-repair` (the base + the repaired file);
- `wt-land` (the tip + the repaired file + the drafted status edits).

`patchrepo/` is a scratch clone with alternates, used for `git am` and for the landing
rehearsal.

Lean ran only through `tools/leanelab.sh` (`scripts/elab.sh`), one elaboration at a time. Runs
lost to the maintainer's session restart were re-run. There was no build or cache command. The
screens ran under the lock, niced. No delivered script or Lean file was run; the worker's probe
was compared byte for byte with the brief's, and the brief's copy was elaborated.

## (a) Integrity and scope

| # | Check | Result | Evidence |
|---|---|---|---|
| 1 | Bundle | `verify` okay; one ref `HEAD` = `189e4675`; sole prerequisite the base | out/04 |
| 2 | Commits | 19, linear, first parent the base. Author `C1 fill agent <fill-agent@campaign>`. Times 05:18:50–09:03:56Z, inside the item's 05:18:49Z + 4 h. The final Lean commit `ed9cb1ad` is at 08:44:41Z | out/05 |
| 3 | Files per commit | 16 commits touch only the owned file. `d1a49114` touches the owned file and 11 `evidence/` files. `9904c7d2`, `fefcaefa`, `189e4675` touch only `evidence/` (logs, probes incl. two `.lean` files, a nested bundle, a copy of the patches) | out/05b, out/05c |
| 4 | Patch series | `git am` of the 19 patches at the base reproduces all 19 trees exactly; owned file `7d1657b3` | out/06b |
| 5 | Delivered file | = the head blob `7d1657b3`, SHA-256 `4eff5210…a7480`; 2,419 lines | out/06 |
| 6 | First edit | `6f6ca79b`'s file = the overlay (`8d445ae6`) byte for byte. Base → overlay is exactly the four imports after line 8 and the 20 privates after the replay canonizer's `sorry` | out/07, out/09 |
| 7 | Regions | overlay → head: 3 hunks. 134 lines after overlay 716 and 48 after 717, both in home (b) (99–717); `sorry` (767) → 1,469 lines (c). Byte-identical: overlay 1–716, the target's docstring and statement (718–766 = head 900–948) and `end Turing`. (d) is unused (complete); the partial's status paragraph (`1cc63ed5`) is gone at the head | out/09 |
| 8 | Freeze (`declfreeze`, `privstmt`, `stmtcheck`) | public 3 → 3, none added or removed. The target is the only authorized body change. Private 20 → 25: added `ic_seam_step`, `ic_rewindLeafTM`, `ic_rewind_scan`, `ic_rewind_leaf_run`, `ic_install_phase`; none changed or removed. Every code line of the base and the overlay appears in order (only the `sorry`) | out/10 |
| 9 | Public constants (workflow §4) | head: the 3 publics + **209 compiler auxiliaries** `Turing.exists_ndInterpreterCore._proof_1_N`. No derived instance, nothing else. Not public declarations, no finding | out/15c |
| 10 | Hygiene (1,651 added lines, code only) | no `sorry`, `admit`, `axiom`, `unfold`, `delta`, `set_option`, `open`, `section`, `variable`, `attribute`, `native_decide`, `noncomputable`, `simp_all`, `aesop`. To inspect: 10 unrestricted `simp`/`simpa`, 8 `norm_num`, 26 `decide`, 60 `show`, 70 `rfl`, 3 `dsimp only`. All pass S2 after the repair (check 27) | out/11 |
| 11 | Widths | no line over 100 characters (two lines over 100 bytes, both the overlay's); widest added line 96 | out/11, out/11b |
| 12 | Size | 769 → 2,419 lines; 3 public / 25 private (lint INFO). REPORT's "1,866" is stale (F4) | out/34 |
| 13 | Public-facing text | the 58 added comment/docstring lines have no campaign label, path, date or session word; the "Phase N" comments inside the proof are descriptive. Every new proof with a body has a literal "Proof sketch" | out/35 |

## (b) Elaboration and axioms

| # | Check | Result | Evidence |
|---|---|---|---|
| 14 | Delivered file, base, `oleans-lg4c2` | exit 0, 46 s; **only** `95:8 declaration uses 'sorry'` | out/13 |
| 15 | Delivered file, tip, `oleans-lu2sc1` | exit 0; the same single warning | out/40 |
| 16 | Axioms at the base (in-module copy, 30 prints + admission walk + external-dependency walk, `lg4c2`) | target `[propext, sorryAx, Classical.choice, Quot.sound]`; direct `sorryAx` users `[exists_replayCanonizer, exists_inputWindowCopyTM, exists_seamLayoutTM]`. The window copier appears only because of the snapshot (row "Snapshots"). `ic_table_call`, `ic_layout_call`, `ic_window_call` carry `sorryAx`, as the pre-ship said. **The 5 new privates and the other 17 are within the standard three.** No other file's private and no other module's equation/unfolding lemma is reached | out/15, out/16 |
| 17 | Axioms at the tip (`lu2sc1`) | target's direct `sorryAx` users: **`[Turing.exists_replayCanonizer]`**. `exists_seamLayoutTM`, `exists_inputWindowCopyTM`, `ic_layout_call` and `ic_window_call` are standard. `ic_table_call` keeps the canonizer's | out/17, out/16 |
| 18 | Against the worker's `axioms.log` | its 2 prints (target, bridge) are equal to mine. The brief asked for every new private (F4) | out/15, `axioms.log` |
| 19 | TCSlib constants reached (target + 25 privates) | 189: 88 theorems, 52 semireducible and 25 reducible definitions (projections, `Cfg.Halted`, `StepBlock.Ph`, a `casesOn`), 12 inductives, 12 constructors. From CodeSimulator only `serializeK`, `serializeK_eq`; from Deterministic/Finite only model primitives and their lemmas | out/18, out/18g |

## (c) Correctness, route and rule 10

**The construction** (head 949–2417). Its parts:
- **Tapes.** `K = 11 + k₁ + k₂ + CI.k`, with tapes by value:
  - 0 stream, 1 `bits t`, 2 `α`/`src`, 3 counter, 4 window, 5 table, 6 summary;
  - 7–8 the loop's bank, 9 the install's capture, 10 the loop's capture;
  - then the two header passes' blocks and the install's scratch (`ιI 0 = 2`).
- **The machine.**
  `R = seamCompTM (… seamCompTM A₁ (inr ()) A₂ 0 …) (inr .done) (embedSilentTM ι₇ capL ic_loopHost) ⟨false, (.dec .run, true)⟩`,
  twelve phases.
- **Verdicts and `C`.** `accept = inr ⟨true, inr true⟩ ≠ reject = inr ⟨true, inr false⟩`. `C` is
  chosen after `α`, before `x, t, s`.

The proof's correctness rests on the kernel check (rows 14–17). I read every new body.

| Item (brief route) | Status | Notes |
|---|---|---|
| 1–3. Two passes, input rewind between | **as briefed**, but see the leaf (F2) | `ic_header_capture true`/`false` (overlay), joined by `ic_seam_step` (`seamCompTM_run_ofCfg` + `seamCompTM_firstReturn_ofCfg`). The leaf `ic_rewindLeafTM` has 3 `controlAction` states, the third a stationary live exit, with its own trajectory lemma |
| 4. Rewind `bits t`'s tape, counter copy | **as briefed** | `rewindTM_run_ofCfg jbt (bits t) |bits t|`, then `copyTM_run_ofCfg jbt jctr` (framed, not the R3 row) |
| 5. Window | **as briefed** | `ic_window_call` from the suffix (`inputPos = 4|bits t| + 2|α| + 7`); it consumes tape 1's counter, and tape 3 keeps the copy |
| 6–7. Input rewind; rewind `α`'s tape; install | **as briefed** | the leaf again; `rewindTM_run_ofCfg jal α |α|`. `ic_install_phase` embeds the install call (`ιI 0 = jal`, the rest blank = `Cfg.ofWords … (stateWord CI.k α)`, proved field by field) behind `seamReleaseTM`, positive first return. The canonizer runs through the install's per-code cost, not `prefixCanonTM`'s time |
| 8. Layout | **as briefed** | `ic_layout_call K jal jtbl jsm` (`src` the installed tape; three distinct tapes) |
| 9. Rewind the window; loop entry | **as briefed** | `rewindTM_run_ofCfg jwin (x.take t) |x.take t|`. `Rep` by `ic_replay_rep` at an explicit five-tape `dstep`. The junction with `vhostCfg (counterLoopCfg …)` is proved tape by tape through `counter_cfg_eq` and `vhostCfg_*`. `ic_replay_tail` for both clauses |
| Decoded machine (gap 3) | **as briefed, then F1** | `simp only [CodeNDTM.toFinNDTM_tm, _k, _State]` at the start. But the statement's `if` keeps its `Decidable` instance typed at `toFinNDTM`'s fields (out/19c), and the verdict's `rw [if_pos hP]` matches it only by unfolding `CodeNDTM.toFinNDTM` |
| Ledger | **as briefed** | `TPRE` = the eleven phases + dispatches. `ic_time_ledger` with `a = 120 + 22|α| + costI α + CL(|serializeK replayTM| + 1) + CW`, `b = 43`, `w = CW + 2`, `L = |tableBitsK replayTM.tr|`, and `t' = 0` for the total clause. `ring` then `omega` |
| No earlier verdict | **as briefed** | `seamCompTM_runFrom_left` (left-tagged before the last seam) and `_right` with the hosted loop's cut |
| Edge cases | covered | `t = 0`, `|x| < t`, `|s| > t` and arbitrary decodings are instances of the proved universal statement (rewinds at `n = 0`, `min t |x|`) |
| Joins | **as briefed** | seams only. No new host, seam, embedding, parser, layout machine or work-tape rewind; no other file's private |

**Rule 10** (the worker ran no seal: "inspection only").

| # | Check | Result | Evidence |
|---|---|---|---|
| 20 | Seal set | the 46 other-file, semireducible, non-projection, non-instance definitions reached: the last round's 38 + `CodeNDTM.toFinNDTM`, `FinTM.controlAction`, `copyTM`, `embedSilentTM`, `moveInputPos`, `rewindTM`, `seamCompTM`, `seamReleaseTM`. Simp-unfoldable among them: `Action.apply`, `Cfg.init`, `MultiTapeTM.initCfg`, `NDTM.initCfg` | out/18, out/18c |
| 21 | Controls | 46 `rfl` controls (one per sealed definition) + 4 `simp` controls, at the section's top and end. **Unsealed: 100/100 pass** | out/19-C2ControlUnsealed.out, out/19b-control-map-unsealed.txt |
| 22 | **S1 (46 `local irreducible`), delivered body** | **6 errors in the body**: delivered lines 785, 789, 808 (`ic_rewind_scan`), 841 (`ic_rewind_leaf_run`), 2365, 2366 (the target's verdict). Controls: 92/92 `rfl` fail sealed. The 8 `simp` controls pass, as expected under S1 | out/19-C2SealControl.out, out/19b-control-map-S1.txt |
| 23 | S2 (S1 + `attribute [-simp]` on the four), delivered body | the same 6 errors and no other, so no unrestricted `simp`/`norm_num` closes through a `@[simp]` definition. 95 controls fail before Lean's 100-error cap | out/19-C2SealSimpControl.out, out/19b-control-map-S2.txt |
| 24 | Attribution | 785/789/808/841: the error terms are `runFrom cfg (0 + 1)`, `(runFrom cfg 0).state`, `runFrom (runFrom cfg 1) _` (**`MultiTapeTM.runFrom`**). 2365/2366: they pass with all but `CodeNDTM.toFinNDTM` sealed (**`CodeNDTM.toFinNDTM`**) | out/19c, out/19d |
| 25 | **Repair** (proof-only, 4 hunks, asserted edits) | `runFrom` read through `runFrom_succ_eq_step`/`runFrom_zero`. The verdict closed by `simp only [hP, and_self, decide_true, if_true]` and `simp only [hP, decide_false, if_false]`; five candidates were tested sealed and two worked | out/21-repairs.diff, scripts/repairs.py, out/19e |
| 26 | Repaired file | base: 0 errors, the 1 warning. Tip: 0 errors. Axioms equal to the delivered file's on all 30 prints | out/22, out/17b, out/17c |
| 27 | **Repaired: S1 / S2** | S1: **0 body diagnostics** but the stub warning; 92/92 `rfl` controls fail. S2: **0 body diagnostics**; 50/50 controls fail (46 `rfl` + 4 `simp`). Unsealed: 100/100 pass | out/23, out/23b, out/24, out/24b, out/24c |
| 28 | `rw`/`simp`/`simpa`/`dsimp`/`unfold` arguments (added code: 810 occurrences, 210 identifiers) | 36 TCSlib theorems (published field equations, run algebra, the catalog/embed/seam/vhost rows); 1 own declaration (`ic_rewindLeafTM`, own file); the rest local hypotheses/lets and core/Mathlib (`Fin.*`, `Function.update_*`, `if_pos`/`if_neg`, `↓reduceIte`, the three `toFinNDTM_*` field equations). **No other file's definition**, no `unfold` | out/20 |
| 29 | `show`/`change`/`rfl`/`decide`/`norm_num`/bare `simp` | apart from the six sites, each exposes a local `set`/`let`, a projection of a structure literal, an own-file table, `Option.map` on `some`, or `Fin` literals (`decide`). All pass S1 and S2 (rows 27, 23) | out/11, out/19b |

**Rule 11.**
- No R3 row, as a token or among the reached constants (`copyTM_run_ofCfg` is the framed row).
- No other file's private is reached (out/15).
- The token hits (`Cfg.mapState_state`, `FinTM.moveInputPos_neg_val`, words) are collisions with
  public names.
- The 5 new privates are `ic_`-prefixed (out/27).

## (d) Escalations, probes and promotion candidates

**Escalations: none, and I agree.** Every fact the route needs has a public lemma. The six
rule-10 sites have published replacements (rows 24–27), and so does the re-proved scan (F2:
`FinTM.rewind_scan`).

| # | Probe | Result | Evidence |
|---|---|---|---|
| 30 | The brief's `C1CoreCont2ImportProbe` (220 checks), standalone; the worker's copy (`evidence/probes/…`) is byte-identical | base (`lg4c2`): 0 errors, 0 warnings. The worker's `probe-rerun.log`: 0 errors | out/26, out/26d |
| 31 | Extended probe (the 220 + the 12 theorems and 4 definitions reached outside them + `runFrom_zero`, `runFrom_add`; 12 axiom prints) | 0 errors at the base and at the tip. All public; the 12 theorems are within the standard three | out/25, out/26b, out/26c |

The 12 unprobed theorems are `Cfg.inputSymbol_of_zero`, `FinTM.bufferTape_nil`,
`FinTM.moveInputPos_neg_val`, `MultiTapeTM.runFrom_succ_eq_step`, `embedSilentCfg_state`,
`inputSymbolInner`, `moveInputPos_pos_of_ne_right`, `seamCompTM_firstReturn_ofCfg`,
`seamCompTM_runFrom_left`, `seamCompTM_runFrom_right`, `seamReleaseTM_runFrom_pos` and
`stateWord_eq`. The 4 definitions are `CodeNDTM.toFinNDTM`, `moveInputPos`, `seamCompTM` and
`seamReleaseTM` (F4).

**Promotion candidates.** REPORT names five: `ic_header_result`, `ic_capture_return`, the leaf,
`ic_seam_step` and `ic_install_phase`. Roughly by payback, for the maintainer's window:
1. **A published native input rewind with an exact time and a fresh, first-arrival exit.** It
   would retire `ic_rewindLeafTM`/`ic_rewind_scan`/`ic_rewind_leaf_run` (F2), U2-S's
   `ss_inputRewind`/`_run`/`_done` (#147) and `SpaceComplexity/Inclusions`' `b2b_rewindTM`. It
   sits beside `rewind_heads` in `Simulation`.
2. **`ic_seam_step`**: the run equation and first return of `seamCompTM`, used eleven times
   here. U2-S's seek/finish/cleanup scaffold (its F5) is the same pattern.
3. `ic_install_phase`, the release-wrapped embedded install call. UN's setup is a likely second
   consumer.

## (e) Duplication and lint

| # | Check | Result | Evidence |
|---|---|---|---|
| 32 | Screen script | `f4feac91…f181` at the base, head and tip | out/28 |
| 33 | Before (the overlay, the 12-file population, 76 s) | `460 declarations; 118 pairs; 43,576 chars`. = the brief's screen base = the worker's `screen-before.txt` (byte-identical) | out/29, out/32-screens-compare |
| 34 | After (head, 131 s) | `465; 120; 44,131`. = the worker's `screen-after.txt` (byte-identical) | out/30, out/32-screens-compare |
| 35 | New pairs (`pairdiff`) | 2 new, 0 gone. In-file: `ic_rewind_scan`/`ic_rewind_leaf_run` 58% (the run lemma calls the scan; the shared one-step scaffold). **Cross-file: `ic_rewind_leaf_run` reproduces `InputWindow::iw_one` 85/124 = 69%** (F3) | out/32, out/32b |
| 36 | The 69% pair's text | three fragments: `MultiTapeTM.runFrom_succ_eq_step` (32), `rw[MultiTapeTM.runFrom_zero,` (28), `MultiTapeTM.step_of_someh` (25). `iw_one` is a 124-character one-step lemma made of those names. Not a copy family; the same kind as the base's `ic_verdictTM_run`/`iw_one` 83/124 = 67% (in the screen base, accepted) | out/32b |
| 37 | ≥ 90% | none with an owned-file declaration (max 69%). The four ≥ 90% pairs are other files', already in the base | out/30 |
| 38 | Extra screen (outside the population): head + `Simulation`, `SpaceComplexity/Inclusions`, `Build/InputWindow`, `Build/Rewind` | three more cross-file pairs. **`ic_rewind_scan` reproduces `Simulation::rewind_scan` 479/945 = 51%**: the induction skeleton, with 118- and 102-character segments (F2). `ic_rewindLeafTM` ↔ `Inclusions::b2b_rewindTM` 51%/57%: the `controlAction` table shape that `rewind_scan`'s hypothesis requires (a required shape, not a finding) | out/33-screen-extra.txt, out/33-rewind-vs-published.txt |
| 39 | Duplication ledger (workflow §4) | cross-file reproduced text 479 + 107 + 85 = 671 of 80,793 code characters, **0.83%**, far below one fifth. The re-proved scan is a "private copy of existing proved material" and belongs in the ledger | out/33b |
| 40 | Lint, `TCSlib/Complexity/TuringMachine` | base `0 FAIL, 63 WARN over 82 files`; head `0 FAIL, 64 WARN`. The new WARN is the size (not a driver, ground rule 8). Tip `66` → tip + file `67`, the same single WARN | out/34 |

## (f) Sweep and environment (addendum v2.4, Parts 1 and 3)

| Item | Recorded | Evidence |
|---|---|---|
| Preflight 05:11:11Z | 4 CPUs; cgroup v1, no limit, so headroom = MemAvailable 15,975,212 kB = 15.24 GiB (≥ 4); `oom_kill` 0; 26,517,278,720 B = 24.70 GiB free on ext4 (≥ 12); after the toolchain 22.29 GiB (≥ 8). = REPORT = the session report (its "26.5 GB" is decimal GB) | out/37-environment.txt, `preflight.log` |
| Cache (Part 3, item 2) | one narrowed fetch; 1,023 attempted, 1,023 downloaded, 1,023 unpacked, "Completed successfully!". No pre-populated store (unlike megafill B's F4). **41 roots = my computation** from the 118-module list | out/37, out/37-mathlib-roots.txt, `cache-get.log` |
| Bootstrap | the 38 upstream modules (37 + the owned file = my closure) at the overlay, 05:20:50–05:29:54Z, no failure. The remaining 80 were first built by the final sweep, which Part 1 item 5 allows. Part 3 item 3.2 asks for the whole list (F6) | out/31, out/35-up-head.txt |
| Final sweep | 80 modules, 08:44:41Z (the final Lean commit's minute) to 08:59:16Z, one completed run each, 0 errors. `CfgRecord`'s first run was SIGKILLed (137, 08:50:56Z) and rerun at 08:53:07Z: the disclosed duplicated launch. The orphan's output is not in the log. "sweep exit 0" | out/31, `item1-final-sweep.log` |
| Owned module, final | 09:00:34Z, exit 0, the replay canonizer's warning only. Its log is in the bundle only | out/31a |
| Sorry census | bootstrap + sweep + owned final = **37 in 17 modules = the base's 38 minus the target**, by name. The shipped `SORRY-DIFF.txt` compares only the sweep's 80 with the full 118-module base list (10 spurious DIFFs, "NDCodeSimulator 2 vs 0") | out/31 |
| Item 6 / `/usr/bin/time` | absent; start/end times only, no per-module memory (disclosed) | logs |
| Bans | no `lake build` and no unfiltered `lake exe cache get` in any log | logs |
| Checkpoints | only cp4 is named ("at the phase-11 boundary"); it is in neither `exchange/inbox` nor `archive`. Its state is the bundle's `9904c7d2` | out/37 |

## (g) Landability

- **The owned file is unchanged from the base to the tip** (`2d41f8f4`). Upstream, the only
  change since the base is SeamLayout (#145, statement unchanged, now proved). Against
  `lu2sc1`, which is exact for all 38 upstream modules, the delivered and repaired files elaborate
  with the 1 warning (out/36, out/36c, out/40, out/51).
- **Landing rehearsal** (scratch clone): `git am -3 --include=TCSlib/Complexity/TuringMachine/NDCodeSimulator.lean`
  of the 16 Lean patches (0001–0011, 0013–0017) onto `97299639`. It applies cleanly, preserves
  the authorship, touches only the owned file and gives the delivered blob `7d1657b3`. The repair
  on top gives `0c0fe25c` (out/39).
- **This landing's closure** (`mkdownmulti.py`, root excluded) is 4 modules: `NDCodeSimulator`,
  `Diagonalization/NTimeHierarchy`, `Diagonalization`, `TuringMachine` (out/38-down-tip.txt).
- **Merged-tree replay** (never compose snapshots; out/38-merged-replay.txt):
  - landing directly on today's tip: from a fresh copy of `oleans-lu2sc1`, the 6-module closure
    of the files that differ from its tree `28150fc1` (NDCodeSimulator, plus `UniversalK` and
    the facade, which differ because #147 has not merged): `NDCodeSimulator`, `NTimeHierarchy`,
    `Diagonalization`, `UniversalK`, `SelfUniversal`, `TuringMachine`;
  - after #147 merges (its tree = `lu2sc1`'s): the 4 modules only;
  - after #149 merges: from its merged tree's snapshot `oleans-lspapi`, the closure of every file
    changed since that tree.
- **Overlaps.**
  - **#149** (`Deterministic`, `Finite`; closure 324 modules) contains all 4 of this landing's
    modules. It only adds two public lemmas (`spaceUsed_eq_sum`,
    `MultiTapeTM.spaceUsed_le_of_abs_le`) and changes `WindowRun`, which is not upstream. No
    constant R reads changes (out/43, out/18g). Whichever lands second replays the shared
    modules. Landing R first would force #149's 324-module replay to be redone, so land R after
    #149.
  - **#147** (`UniversalK`; closure UniversalK, SelfUniversal, the facade): shares only the
    facade module, and the facade *file* only if the drafted facade status edit is taken
    (different hunks: lines 131–133 against #147's 244–250).
  - **Item 2** (UN cont1, `NTimeHierarchy`; closure 2): shares `NTimeHierarchy` and
    `Diagonalization`. It cites R's frozen statement only; either order works, and the second
    replays the two.
  - **Item 3** (canonizer cont7, `CodeSimulator`; closure 10): contains all 4. R reads only
    `serializeK`/`serializeK_eq` from `CodeSimulator`, so it is unaffected while item 3's
    statements are frozen. Item 3's replay includes NDCodeSimulator (about 46 s).
- **Name clashes:** none. The new names are private; the only new public constants are the
  target's `_proof_1_N` auxiliaries (row 9).
- **Expected after landing:**
  - NDCodeSimulator: 1 sorry warning (the replay canonizer);
  - the order list's sorry census drops by exactly the target's entry;
  - the target's direct `sorryAx` users `[exists_replayCanonizer]`;
  - UN's `exists_timed_universal_NDTM` (item 2) then rests on this proof and the replay
    canonizer.

## (h) Recommendation

**Not yet clear to merge.** The landing PR is not open, not replayed and not gated, and the
rule-10 repair is not yet in a commit. It becomes clear once the PR (on the campaign branch, not
stacked) carries the repair and the status edits, its merged-tree replay has passed and its fill
gate is recorded.

**Land (full): yes**, by a maintainer PR into `complexity/arora-barak-ch3-4`.
- **Order.** After #149 (recommended; otherwise #149's 324-module replay must be redone), and
  preferably after #147, which makes the replay 4 modules. Its order against items 2 and 3 is
  free.
- **Commits.** `git am -3 --include=TCSlib/Complexity/TuringMachine/NDCodeSimulator.lean` of these
  16 patches from the zip, in order. They are the bundle's commits (prerequisite `6cfee544`; the
  owned file is unchanged at the tip):
  - `6f6ca79b940ae585f164f96bed5bdddedd59c30a`, `f9a269e194394bab52542f58e1260ceb9b9f75ab`;
  - `aa571773ab76faf3410f3e022f13048623cbfdfd`, `a5d53a16cefdae6c500c0b70dfc70b11191efdde`;
  - `40a9dfb0134c57b3293c03aa4cd4458398edcf5c`, `94f5bbba18f2be25b6054418c46558ecdd563e90`;
  - `df9b9fa11573b02937c64f0e7246df07d0bee757`, `2f180636a74973d50671198f060e3731024a4208`;
  - `514b65474fd5b14d8000876f469fb2c1caccb818`, `1cc63ed52c6e246dab7c9d551a29b67dddd0fac5`;
  - `d1a49114e5dc2a02020123c91a853df128b1c7f5` (owned file only);
  - `35b3432ac646bc804a9db2be9a74f44e57409e66`, `07508b2dce162380607f7d3be362b31c5d14856a`;
  - `64d9850afb4be13bcdea09e6d68f3b8c974ee4dd`, `9bb89089dd976a12902189b53f0d0016aeb4b1ba`;
  - `ed9cb1ade76b99cadcd692ec2126beff4801d422`.

  **Skip** `9904c7d2…`, `fefcaefa…` and `189e4675…`, and `d1a49114`'s `evidence/` part. The
  delivery's logs go to the campaign records instead (non-`.lean`, pushed directly). Link
  `.lake/packages` in the PR worktree.
- **Maintainer commits in the same PR**, all checked at the tip (0 errors, 1 warning; widths ≤
  100; lint 0 FAIL, 67 WARN = the tip's 66 + the size; out/51, out/51b, out/51c, out/50b):
  1. **The rule-10 repair** (`out/21-repairs.diff`, proof-only), with the message "Read the
     rewind leaf's runs and the verdict through published equations".
  2. Status, `NDCodeSimulator.lean` line 53: "`Turing.exists_ndInterpreterCore` — the
     interpreter core `R` (sorried)." → "… (proved, modulo the canonizer)."
     (`out/50-landing-edits-module.diff`).
  3. Facade, `TuringMachine.lean` lines 132–133: "The canonizer and the core are sorried." →
     "The core is proved; the canonizer is sorried." (`out/50-landing-edits-facade.diff`).
  4. Optional (F7): an `**Implementation.**` paragraph at the end of the target's docstring. It
     names the twelve phases in the order the proof runs them and the reason the window precedes
     the installation (drafted in `out/50-landing-edits-module.diff`).
- **Records** (non-`.lean`, direct): the duplication-ledger entry for `ic_rewind_scan` (F2,
  0.83%). This review's REPORT corrections (F4).
- **Review table for the PR body:**
  - integrity: 34/34 sums, bundle, 19 commits, patches = bundle = file;
  - scope: regions (a)–(c), statement and docstring byte-identical, 20 privates verbatim + 5
    `ic_`, 3 → 3 public;
  - elaboration at the base and at the tip: the replay canonizer's warning only;
  - axioms: `sorryAx` only through the replay canonizer at the tip;
  - rule 10: six sites repaired; the S1 and S2 seals clean with 46 + 4 controls;
  - probes 220/238, 0 errors;
  - screen 460 → 465 declarations, 118 → 120 pairs, one idiom cross-file pair (F3);
  - lint 0 FAIL; census 38 → 37.

**What remains in the file:** `Turing.exists_replayCanonizer` (wave 2). Its sketch is in the
file; once it is proved, R and UN's `exists_timed_universal_NDTM` are admission-free.

## Findings (detail)

**F1 — rule 10, six definitional closures (major; resolved by the review's repair).**
- *Claim.* Ground rule 10 forbids a step that closes only because another file's definition
  reduces, and requires a seal test with a failing control. The delivery ran no seal ("not
  re-run this round (budget)"), yet states that the inspection "found no definitional closure".
- *Evidence.* With the 46 reached other-file definitions sealed (out/19-seal-summary.txt), six
  sites fail:
  - `ic_rewind_scan`, delivered lines 785, 789 and 808: `show (ic_rewindLeafTM k).step cfg = _`
    against `runFrom cfg (0 + 1)`, and `exact hs` against `(runFrom cfg 0).state` (twice);
  - `ic_rewind_leaf_run`, line 841: `show … runFrom (step cfg) _` against
    `runFrom (runFrom cfg 1) _`;
  - the target's verdict, lines 2365–2366: `rw [if_pos hP, decide_eq_true hP]` (and the negative
    case). The statement's `if` carries a `Decidable` instance typed at
    `(c.decode α).toFinNDTM`'s fields, which the sanctioned `simp only` transport leaves untouched
    (out/19c). `rw` must identify it with `hP`'s proposition, and that unfolds `CodeNDTM.toFinNDTM`
    (bisect: out/19d).

  The first four unfold `MultiTapeTM.runFrom`, a machine-model primitive the rule says to read
  through its lemmas. The last two unfold `CodeNDTM.toFinNDTM`, which the brief singles out
  ("only through its three field equations").
- *Resolution.* Apply `out/21-repairs.diff`:
  - `runFrom_succ_eq_step`/`runFrom_zero` in the two lemmas (`htime` restated as
    `p + 1 = p - 1 + 1 + 1`);
  - `simp only [hP, and_self, decide_true, if_true]` and
    `simp only [hP, decide_false, if_false]` at the verdict.

  The repaired file passes S1, S2 and all controls (rows 25–27) with unchanged axioms. Lesson for
  later briefs: the target's `if` keeps the bundled machine's instance after the `toFinNDTM_*`
  transport; prescribe closing it by `simp only` on the hypothesis, not by `rw [if_pos …]`.

**F2 — the input rewind re-proves `FinTM.rewind_scan` (minor; decision).**
- *Claim.*
  - The route says "an input rewind (the head to `1`; your leaf through `FinTM.rewind_heads`)".
  - Ground rule 7 allows a leaf table "run by `FinTM.rewind_heads`".
  - Ground rule 5 says "Cite proved material; never re-prove it".
- *Evidence.* `ic_rewind_scan` (54 lines with its docstring) re-derives the scan by its own
  induction. On the v3
  metric it reproduces 479/945 = 51% of `Simulation::rewind_scan`: the same zero/successor
  skeleton, and the same `hm : moveInputPos … .pos = 1` block (out/33). The leaf's scanning row has
  exactly the shape `rewind_scan`'s hypothesis takes, so `rewind_scan` applies to it directly.
  Only the "stays scanning before" clause, which the seam's first-return cut needs, is not
  published. U2-S (#147) got that clause from the published rows through a four-state leaf with a
  stationary exit; `b2b_rewindTM` uses `rewind_heads` too. `Simulation` is outside the brief's
  12-file population, so the brief's screen could not flag it. REPORT presents the leaf as
  "ground rule 7's allowed leaf" without the deviation.
- *Resolution options:*
  1. **(a) Accept (recommended).** The proof is leaf-local, private, 0.83% of the file, and
     correct. Record it in the duplication ledger, and retire it with promotion candidate 1 (a
     published input rewind with a fresh exit, which also retires U2-S's three `ss_inputRewind*`).
  2. **(b) Rework before landing.** Replace `ic_rewind_scan` by `FinTM.rewind_scan` and a
     four-state leaf with a stationary exit, as U2-S does: about 60 lines, plus a re-review.

**F3 — one new cross-file pair (minor; decision).**
- *Claim.* The brief: "No new cross-file pair with an owned-file declaration on one side."
- *Evidence.* `ic_rewind_leaf_run` reproduces `InputWindow::iw_one` at 85/124 = 69% (out/32b).
  `iw_one` is a three-line lemma: `runFrom_succ_eq_step'`, `runFrom_zero`, `step_of_some`. The
  shared text is those three names. The screen base already holds the same kind of pair against
  the same lemma (`ic_verdictTM_run`, 67%). The worker disclosed it.
- *Resolution.* Accept it as an idiom pair (recommended). The alternative is to reword the two
  `rw`s to dodge the metric, which buys nothing.

**F4 — records (minor).** For the PR body and the records:
1. Size: 2,419 lines, not 1,866 (REPORT's size and lint lines are from the partial state).
2. The "beyond the probe … none" statement is wrong: 12 theorems and 4 definitions are outside the
   220. They are all public and proved; the extended probe has 0 errors (rows 30–31). The worker
   did not run the copy of the probe that rule 10 requires.
3. `SORRY-DIFF.txt` is not the census REPORT quotes (row "Sorry census"). The owned module's final
   check is only in the bundle.
4. The axiom log has 2 prints; the brief asks for every new private (row 18).
5. "Escalations: none (… the stop is the budget)" is a partial-era sentence. "Over-100 lines 206
   and 946" means bytes, not characters.
6. Checkpoints: one zip, cp4, where the brief asks for one per phase. It is not in the exchange
   folder.
7. The session report's "modulo exactly the two cited stubs (exists_replayCanonizer, and
   serialize_eq_tableBitsK's bridge is clean)" is garbled. REPORT's "the replay canonizer and the
   seam layout" is the accurate wording at the base.

**F5 — landing mechanics (minor).**
- *Evidence.* Three commits carry only repository-root `evidence/` files. `d1a49114` mixes the
  owned file's style wrap with 11 such files, among them `evidence/probes/*.lean` and a nested copy
  of the bundle (out/05b, out/05c). Commit subjects carry campaign labels ("C1 R cont2",
  "(partial)").
- *Resolution.* `git am -3 --include=<owned file>` of the 16 Lean patches (rehearsed, out/39).
  Keep the authorship (workflow §4) and the subjects, or squash with a public-facing message
  (decision 5).

**F6 — environment and process (note).** Both points were disclosed and neither changes a
result:
- the 80 non-upstream modules were first built by the final sweep, which ran on the final file;
- a duplicated sweep launch was briefly a second Lean process (`CfgRecord` killed, then rerun).

Every module has one completed run, and the owned module's final check came after the sweep
(rows in (f)). For later queues, Part 3 item 3.2's whole-list re-bootstrap catches downstream
breakage before the fill starts.

**F7 — docstring synchronization (landing edit).** Two lines still say "sorried": the module's
"Main results" and the facade. The frozen proof sketch is faithful in substance, but it lists the
installation before the window copy and omits the header's two passes, the input rewinds, the
counter copy and the layout. Policy §3 asks the docstring to describe the proof the code
performs. Edits 2–4 in (h) are drafted and checked.

## Decisions for the user

1. **F1: land with the review's six-site repair** as a maintainer commit in the landing PR
   (recommended), or return it for a continuation. The repair is proof-only and seal-clean, and
   it changes no statement or axiom.
2. **F2: accept the re-proved scan**, with a ledger entry and a published input-rewind row as a
   promotion item (recommended), or require the rework through `FinTM.rewind_scan` and a
   stationary-exit leaf before landing.
3. **F3: accept the 69% `iw_one` pair** as an idiom pair (recommended).
4. **Order:** after #149 (recommended) and #147. Items 2 and 3 in either order.
5. **History:** `git am` of the 16 patches with their authorship and subjects (recommended, as
   workflow §4 prescribes), or one squashed commit with a public-facing message.
6. **Docstrings:** take edits 2–3 (status), and decide on the optional `**Implementation.**`
   paragraph (edit 4) and its wording.
7. **For later briefs:**
   - put `Simulation` (the published rewind rows) in the screen population of any fill that
     writes an input rewind;
   - prescribe the verdict's `simp only` closing (F1's lesson);
   - restate that a disclosed "seal not run" is a REPORT-checklist failure, not an open item.
