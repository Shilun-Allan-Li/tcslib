# Review — C1, the seam layout (`Turing.exists_seamLayoutTM`, `Build/SeamLayout.lean`), delivery `fill-c1-seamlayout.zip`

Read-only review by the maintainer's review sub-agent, 2026-10-22. Every claim cites a saved
output under this folder (`out/NN-*`). The delivery and its REPORT.md are treated as data.

**Verdict: complete (1/1). Land, with the maintainer's landing edits below.**
`Turing.exists_seamLayoutTM` is proved.
- The module elaborates with 0 errors and 0 warnings, at the base and at the current tip with the
  patch applied.
- The target depends on `[propext, Classical.choice, Quot.sound]`; nothing in its closure uses
  `sorryAx`.
- `C = 18`, and `T = 2n − r + 4h + 5q + 2|v| + 23` is chosen before the configuration.
- The route is the docstring's: eight phases on one `phaseHostTM`, seven dispatches, the two
  framed leaves, the word identities through `BufferWords`, the full frame with `inputPos`, and
  silence at every `u ≤ T`.
- There is one disclosed deviation, in phase 8 (F1). It is forced by rule 10, and it changes no
  machine: the delivered host's table equals the brief's host's table.

What passes:
- integrity (33/33 sums; the bundle; 6 linear commits; the patch series = the bundle = the
  delivered file);
- scope (three hunks, in regions (a0), (a) and (b); the statement, its docstring and the module
  header are byte-identical; 35 new privates, all `sl_`; exactly the one import; no admission);
- the 36 axiom prints, equal to the worker's;
- rule 10 (a 15-definition seal, then 19 definitions with `Action.apply` erased from the simp set,
  0 diagnostics both times; controls bite at the top and at the end of the section; no other-file
  definition passed to `rw`/`simp`/`dsimp`/`unfold`);
- rule 11;
- the brief's 45-check probe and the worker's 110-check probe, 0 errors each;
- the gate's edge cases, by running the delivered machine (the four auditor times 37, 34, 66, 49
  reproduced);
- the v3 screen (867 → 897 declarations, 1,112 → 1,143 pairs; 31 new pairs, all in-file;
  0 cross-file; none at 90% or more; no hazard pair), equal to the worker's;
- lint (0 FAIL; the one new WARN is the file size);
- the worker's 94-module sweep (35 → 34; every other sorry unchanged by name).

Findings (none blocks landing):
- **F1 (route, decision: accept).** The brief has phase 8 run through
  `MultiTapeTM.runFrom_mapState_of_agreeOn` with the trivial guard. The delivery instead gives
  phase 8's `done` a self-redirect (`sl_red .clearHead .done = some ⟨.clearHead, .done⟩`), so that
  `phaseHostTM_run`'s first component covers the clear up to and including its exit time. REPORT §5
  discloses this.
  - The brief's route cannot be followed under rule 10. The transport's `hagree` is the host's
    table on a non-redirected state, and no published lemma states it. The only lemma naming
    `phaseHostTM` is `phaseHostTM_run` (out/21). The table fact closes by `simp only
    [phaseHostTM, hs]`; without the unfolding, `simp only [hs]` makes no progress (out/21b).
  - That `simp only` closes it **even with `phaseHostTM` sealed** (out/21b). So REPORT's statement
    that the seal would fail on it is wrong. The barrier is rule 10's ban on unfolding, which only
    an inspection of the proof catches.
  - **The machine is unchanged.** The clear row's live `done` is a silent stationary self-loop, the
    same action as the dispatch. The delivered host's `tr` equals the trivial-guard host's `tr` as
    functions, by `funext` and `rfl` over every state (out/21c). The eight phases, the seven
    dispatches, the ledger and `C` are as briefed.
  - Process lesson: the pre-ship did not check that phase 8's bridge is public.
- **F2 (scope, minor).** `deriving DecidableEq, Fintype` on the three private inductives
  generates six instances with **public** names: `Turing.instDecidableEqSl_Key`, `…Sl_PairPhase`,
  `…Sl_SplitPhase` and `Turing.instFintypeSl_Key`, `…Sl_PairPhase`, `…Sl_SplitPhase`, with their
  auxiliaries (out/15, `MODULE PUBLICS`).
  - Their types are private, so they cannot fire outside the file. No name clashes at the tip or at
    #139's or #143's head (out/41).
  - The landed `xr_St` (`ExhaustiveReplay`) and `wl_Phase` (`WindowRun`) do the same. The chapter-1
    campaign called this the "2D trap".
  - Accept per precedent, or replace the `deriving` clauses by explicit `private instance`s.
- **F3 (policy §3, minor; decision).** 14 private proofs are over 20 lines and have no "Proof
  sketch" paragraph (out/49). The largest are `sl_unarySplit_copy` (117 lines),
  `sl_pairSkipTM_run` (91), `sl_phase6` (91), `sl_unarySplitTM_run` (70) and `sl_phase4` (70).
  Every one has a docstring that states its contract. The target's sketch matches the proof. This
  is the same debt as C1-E's F3.
- **F4 (records, minor).** REPORT is inaccurate in these places; none changes a conclusion.
  1. It lists `FinTM.bufferTape_of_neg` among the lemmas the proof cites (§CP2, for
     `sl_reverse_read`; §6). The proof never uses it. It uses `bufferTape_left`, and `_of_neg`
     appears only in the frozen docstring (out/25).
  2. Its paths are `evidence/logs/…` and `evidence/probe/…`, but the zip has `logs/` and
     `probes/`. The `final-module-check.log` it cites is not in the zip.
  3. §5's claim about the seal is wrong (F1).
  4. `logs/manifest-check.log` ends `MANIFEST CHECK: FAIL`, with four `MISMATCH` lines. REPORT
     reads them as "absent, not mismatched" but does not quote the FAIL ((f)).
  5. The final sweep checked `SeamLayout` at 03:32, between commit 5 (03:25) and commit 6
     (03:39). Only the facade was re-checked after commit 6. My elaborations cover the head
     (out/13, out/31).
- **F5 (landing hygiene, minor).** The six commit subjects begin "C1 seam-layout fill". Their
  messages carry `Co-Authored-By: Claude Fable 5` and a `Claude-Session:` trailer with a private
  session URL, and the author is `Fill agent <ragavanbsco@mit.edu>` (out/05). Earlier fill landings
  used subjects named by module ("ExhaustiveReplay: …") and had no session trailer. Squash or
  reword at landing.

## Inputs

| Input | Identity | Evidence |
|---|---|---|
| Zip `exchange/inbox/fill-c1-seamlayout.zip` | SHA-256 `18442008…3083a` (as given), 34 files, no C, shell or Python file | out/01, out/03 |
| Extraction `$S/inbox-seam/fill-c1-seamlayout/` | every member byte-equal to the zip; no unsafe entry; CRC OK | out/02 |
| `SHA256SUMS` | 33/33 OK; covers every member except itself | out/03 |
| Brief, dispatch copy `exchange/outbox/fills/c1-fill-seamlayout.md` | `85ea4a61…4bffec` (as given) = the base's `campaign/fills/c1/briefs/c1-fill-seamlayout.md` (`98dfbbcb…`) with its three `@ANCESTOR@` := `1c06ea94…`. The records copy (`wt-hk`) = the base copy | out/07 |
| Addendum v2.3 `exchange/outbox/fills/fill-environment-addendum.md` | `1ea7a376…` = the base's `campaign/standards/` copy (as REPORT says) | out/07 |
| Brief inputs (overlay, 45-check probe, 9-file population, 94-module order list, base sorries, screen base, pre-ship log) | base blobs = records blobs; the overlay = the base file + the one import | out/07 |
| Base `1c06ea94d0eb9226c355ffa8941aa6ed4ab9c1d6` | a records commit; TCSlib tree `0fcc0e49` = `e2bc85eb`'s (#140's merge) | out/04 |
| Head `09773a665e5409a66ddc71a42f566efe74e690d8` | the bundle's only ref (`HEAD`), fetched into `refs/review/c1-seamlayout` | out/04, out/05 |
| Snapshot | `oleans-lbw2` (#140's replay; base and tip, since the module's 17-module upstream is unchanged, (g)) | out/36 |
| Campaign tip | **It moved during this review.** It went `28bd2e21` → `1d4fcf3e` → `2ff214c5` (#137 merged, 04:21Z) → `58583249` (records only: the megafills A/B issued, gates 56/58 findings, #144 opened). The TCSlib tree is `268944d6` at both of the last two, so the tip analysis at `2ff214c5` holds. Open Lean PRs: #139 (`Build/StepClock`, `1cd66f1b`), #143 (`Build/ZoneRebalance`, `c60ed898`) and #144 (`ExhaustiveReplay`, docstrings, `65e140d1`) | out/36, out/43, out/44 |

Review worktrees, all detached under this folder, each with the `.lake/packages` link:
- `wt-base` (base), `wt-head` (head) and `wt-patch` (the base with the series `git apply`'d);
- `wt-tip` (`2ff214c5` with the series `git apply`'d, uncommitted).

Lean ran only through `tools/leanelab.sh`, one elaboration at a time. Probe sources are in
`wt-head/ReviewScratch/`, with copies (and the two delivered probes) in `probe/`; scripts are in
`scripts/`. No build command and no cache command was run. The screens ran under `nice -n 10`,
one at a time, each only when no other screen was running.

## (a) Integrity and scope

| # | Check | Result | Evidence |
|---|---|---|---|
| 1 | Bundle | `verify` okay. One ref, `HEAD` = `09773a66`. Its sole prerequisite is the base `1c06ea94` | out/04 |
| 2 | Commits | 6, linear, no merges; the first parent is the base. Each touches only `Build/SeamLayout.lean`; in all +1636/−1 | out/05 |
| 3 | First commit `d6dd89ab` | adds exactly `import TCSlib.Complexity.TuringMachine.BufferWords` after line 7 (the region (a0) edit), together with checkpoint 1. Its first 12 lines = the overlay's | out/05, out/07 |
| 4 | Patch series | the 6 patches applied at the base give the head blob `483be51b`. Each patch equals `git format-patch` of its commit, except the git-version trailer (`2.43.0`) | out/06 |
| 5 | Delivered `src/` file | = the head blob (SHA-256 `e0f0c89f…`) | out/06 |
| 6 | Regions | Three hunks: (a0) +1 import after base line 7; (a) 1391 lines inserted after the blank base line 35 (overlay 36), before the target's docstring; (b) base line 118 (overlay 119) `  sorry` → 244 lines. (c) is unused (complete). The module header and docstring, the target's docstring and statement, and the closing lines are byte-identical | out/09 |
| 7 | Freeze (`declfreeze.py … exists_seamLayoutTM`) | public 1 → 1, none added or removed. The target: "authorized body change" (statement unchanged). Private 0 → 35, all `sl_` | out/10 |
| 8 | Hygiene (1636 added lines, code only) | no `sorry`, `admit`, `axiom`, `unfold`, `delta`, `set_option`, `open`, `section`, `variable`, `attribute`, `native_decide`, `extern`/`implemented_by`, `unsafe`/`partial`, macro/elab, `#eval`/`#print`, `noncomputable` or `Classical`. The 7 `decide` tactics are all `sl_Key.X ≠ .clearHead` on the file's own key | out/11 |
| 9 | Widths | no line over 100 characters (max 99 characters, 100 bytes) | out/11, out/11b |
| 10 | Size | 120 → 1,755 lines; 1 public / 35 private (lint INFO) | out/34 |
| 11 | Generated public names | six derived instances with public names, plus auxiliaries (F2). No other public constant beyond the target and its `_proof_*` auxiliaries | out/15 |
| 12 | Public-facing text | the 118 added comment/docstring lines contain no campaign label, path or date. The one hit, "filled", is a false positive. The commit messages do (F5) | out/35, out/05 |

## (b) Elaboration and axioms

| # | Check | Result | Evidence |
|---|---|---|---|
| 13 | Base file, `oleans-lbw2` | exit 0; `96:8 declaration uses 'sorry'` only. Overlay: `97:8` only (= the pre-ship) | out/12, out/12b |
| 14 | Head file, `oleans-lbw2` | exit 0, **no diagnostics** | out/13 |
| 15 | Axioms: a copy of the module with `#print axioms` for all 36 declarations, an admission walk and a dependency walk | target: `[propext, Classical.choice, Quot.sound]`. Direct `sorryAx` users in its closure: `[]`. All 36 are within the standard three (histogram: 23 / 10 none / 1 each `propext, Quot.sound`, `Quot.sound`, `propext`). Print for print equal to the worker's `axioms.log` | out/15, out/16 |
| 16 | Other files' privates reached | none (dependency walk over all 36) | out/15, out/27 |
| 17 | TCSlib constants reached | 75: 34 theorems, 29 definitions (15 semireducible non-projection non-instance, 10 projections, 4 derived instances), 7 constructors, 5 inductives. `runFrom_mapState_of_agreeOn` is not among them (F1) | out/15 (`.tcslib-consts.txt`), out/17, out/17b |

## (c) Correctness, route and rule 10

**The construction.**
- `L := phaseHostTM (sl_part k src tbl sm) ⟨.skipRest, .run⟩ sl_red` over
  `(i : sl_Key) × sl_Ph i`, with `entry = ⟨.skipRest, .run⟩`, `done = ⟨.clearHead, .done⟩` and
  `C = 18`.
- `sl_part` is skip, skip back, `sl_pairSkipTM`, `sl_unarySplitTM`, walk (`sm`, `(· = sm)`, `.neg`),
  transfer (`src → tbl`), skip back and clear.
- `sl_red` sends each phase's `done` to the next phase's entry; for phase 8, see F1.
- `sl_cfg` is the canonical mid-run configuration. Its fields are the target's nested
  `Function.update` triples over the frame `d`, so the endpoint's tapes, heads, input position and
  output come out definitionally (head lines 1657–1670).

I read the whole file. The theorem's correctness rests on the kernel-checked proof (rows 14–15).

| Item | Status | Notes |
|---|---|---|
| Eight phases, the docstring's order, on one host | **as briefed** | no second host, seam, row or embedding. Each row is cited through its `_run_ofCfg` contract (rule 11, row 27) |
| Seven dispatches; clear's `done` is the exit | **as briefed** | P1–P7 each end at `T_i + 1` = `H.2` of `phaseHostTM_run` (one dispatch); P8 ends at `T_8` exactly (`H.1 T_8 le_rfl`). No terminal halting phase |
| Phase 8's transport | **deviation (F1), accept** | a self-redirect instead of `runFrom_mapState_of_agreeOn`. The brief's route needs an unpublished table fact (out/21, out/21b). The tables are equal (out/21c) |
| Time | **as briefed** | `refine ⟨2 * s.length - r + 4 * (2 * a.length + 2) + 5 * q + 2 * v.length + 23, by omega, ?_⟩` comes before `intro z d`, so it depends on `a, v, q, r` only. `hTsplit` matches the ledger `n−r+1, n+3, h, q+3, q+2, 2|v|+2, h+q+3, 2(h+q)+2` plus 7. The sum checks: constants 23, `2n − r`, `4h`, `5q`, `2|v|` |
| `C = 18` | **as briefed** | `T ≤ 18(n+1)` by `omega` from `hslen`. The slack `7n + 18 − T = h + 3|v| + r` checks by hand |
| Leaves | **as briefed** | `sl_pairSkipTM_run` takes exactly `2|a|+2` steps (induction on `a`, the pair reads from `bufferTape_append_shift` and `pairEncode_eq`). `sl_unarySplitTM_run` takes exactly `q+3` (induction on `q`), writing on `sm` from two cells right with that head ending on the terminator, blanking the terminator's `src` cell without restoring it, and leaving the `src` head one past it. Both contracts are framed over an arbitrary configuration, with the cut at `done` and silence at every `t ≤` the exit. Each docstring says why no row serves it. `step` and `Action.apply` are read through `step_of_some` and `Action.apply_*` only, even for the leaves |
| Word identities | **as briefed** | through `pairEncode_eq` and `BufferWords` (`_append_shift`, `_drop`, `_take`, `_eq_none_of_not_mem`, `_unary`) with `bufferTape_nat`/`_left`. Phase 5's reverse read is the private `sl_reverse_read` (core `List.getElem?_reverse`). Never `serializeK_eq` or StepBlock's privates. `_append_mid` is not used (the pair reads go by induction through `_append_shift`) |
| Frame | **as briefed** | the full triple `Function.update` endpoint for `workTapes` and `workTapePos`, and `inputPos = d.inputPos`, for every frame `d` (other tapes, heads, input and output arbitrary) |
| Silence for all `u ≤ T` | **as briefed** | the output-prefix sandwich (`output_prefix` from 0 and to `T`, then `IsPrefix.eq_of_length`) |
| No earlier `done` | **as briefed** | the eight windows partition `[0, T)`. In phases 1–7 the tag is not `clearHead` (`sl_tagged_ne_done`); in phase 8, the clear row's own cut |
| Edge cases | **checked by running the machine** (out/22) | In a copy of the module I ran the delivered `L` (k = 4, a fourth tape holding cells at −7, −3 and 5 with its head at −3) on 8 instances. These are the auditor's four (T = 37, 34, 66, 49), `r = n` (three cases), `q = 0`, `v = []`, `a = []`, and all-`false` tables (`v = [f,f,f]`, `[f,f,f,f]`). In every case: the first `done` is at `T` exactly; at `T`, `src` is blank on the window `[−8, n+8)`, `tbl = bufferTape v`, `sm = bufferTape m (· − 2)`, the fourth tape is unchanged, the heads are 0, 0, 0 and −3, and the input position is unchanged; the output is `[]` for all `t ≤ T`; and `T ≤ 18(n+1)`. REPORT checked these by evaluating the closed form only |

**Rule 10.**

| # | Check | Result | Evidence |
|---|---|---|---|
| 18 | Seal set | the 15 other-file, semireducible, non-projection, non-instance definitions the module reaches: `Action.apply`, `Cfg.inputSymbol`, `Cfg.mapState`, `Cfg.workTapeSymbols`, `FinTM.bufferTape`, `MultiTapeTM.runFrom`, `MultiTapeTM.step`, `clearTM`, `moveInputPos`, `pairEncode`, `phaseHostTM`, `skipBackTM`, `skipTM`, `transferTM`, `walkTM`. The second seal adds the 4 derived instances of `SeekPhase`/`SweepPhase` | out/17, out/18 |
| 19 | Seal S1 (the whole `namespace Turing` body in a section, the 15 `local irreducible`) | **0 errors, 0 warnings** | out/19-SLSealHead |
| 20 | Seal S2 (19 names, plus `attribute [-simp] Turing.Action.apply`, the one `@[simp] def` among them) | **0 errors, 0 warnings.** With controls at the top and at the end of the section: exactly 14 errors, the 14 controls (`runFrom`, `bufferTape`, `phaseHostTM`, `mapState`, `skipTM`/`clearTM`, `pairEncode` by `rfl`, and `(a.apply c).state = a.state` by `simp`). S1's controls: 12 errors (the `simp` control passes there, as expected). Unsealed controls: 0 | out/19-* |
| 21 | The worker's seal file (`probes/SeamLayoutSeal.lean`: 21 names at file level, no controls, no simp erasure) | 0 errors (it is the module plus the attribute block, read) | out/19-worker-seal |
| 22 | Rewrite/simp/unfold arguments (671 occurrences, 118 identifiers) | 21 TCSlib theorems, 7 own declarations (`sl_Ph`, `sl_apply_eq`, `sl_bufferTape_unary_int`, `sl_cfg`, `sl_pairSkipTM`, `sl_red`, `sl_unarySplitTM`), and 90 local hypotheses and core/Mathlib lemmas. **No other-file definition.** The 29 `show`s and 113 `rfl`s are covered by the seal (rows 19–20): the `rfl`s close structure projections of the rows' `{ d with … }` endpoints and of `sl_cfg` | out/20 |
| 23 | Unfolding in the eqn-lemma walk | no `X.eq_N`/`eq_def`/`match_N` of a TCSlib definition is reached; the only heuristic hit is Mathlib's `List.IsPrefix.eq_of_length` | out/16 |

**Rule 11.**

| # | Check | Result | Evidence |
|---|---|---|---|
| 24 | R3 rows | 0 bare tokens in the added lines (grep and an independent regex). Among the reached constants are only the framed `skipTM`, `skipBackTM`, `walkTM`, `transferTM` and `clearTM` `_run_ofCfg` rows | out/27 |
| 25 | Other files' privates | none reached; no `_private` token added; every new private is `sl_` | out/27 |

## (d) Escalations and promotion candidates

**Escalations: none, and I agree.** F1 needs no escalation: phase 8 is covered by the public
`phaseHostTM_run`, and the machine is unchanged.

**Import probes (check 5).**

| # | Probe | Result | Evidence |
|---|---|---|---|
| 26 | The brief's `SeamLayoutFillImportProbe` (45 checks; byte-equal to the issued one) | 0 errors, 0 warnings; its output = the worker's `import-probe-after.log` byte for byte | out/24 |
| 27 | The worker's extended probe (110 checks, the issued 45 first, verbatim), standalone and appended to a copy of the head module (so the target checked is the proved one) | 0 errors, 0 warnings each | out/24 |
| 28 | Citations outside the extended list | 25 reached TCSlib constants. All are structural: 10 projections, 7 constructors, the inductive `Action`, 4 derived instances, and `Cfg.inputSymbol`, `Cfg.workTapeSymbols` and `moveInputPos`, which are reached through the statements of `step_of_some` and `Action.apply_*`. **No theorem outside the list.** 10 issued names are not used: the target itself, `runFrom_mapState_of_agreeOn`, `AgreeOn`, `agreeOn_iff` (F1), `bufferTape_nil`, `_eq`, `_of_neg`, `_append`, `_append_mid` and `step_of_halt` | out/25 |

**Promotion candidates.** REPORT says none. For the maintainer's window I note four:
1. **The phase host's last phase**: a published table equation for `phaseHostTM` on a
   non-redirected state, or a "live exit" form of `phaseHostTM_run` (the lockstep window up to
   and including `T` with the guard only before `T` and no `hred`), in `Build/Seam`. F1's
   self-redirect works whenever the last row's `done` is a silent stationary self-loop, as every
   catalog row's live anchor is. Without one of these, each later phase-host brief meets the same
   gap.
2. **`sl_apply_eq`**: the normal form of a silent, input-stationary applied action. It is the same
   fact as `ExhaustiveReplay`'s private `xr_act_apply`, which landed after this base, so the worker
   could not have seen it. One public `Action.apply` lemma beside `Action.apply_workTapes` would
   serve both.
3. **`sl_reverse_read`**: a `FinTM.bufferTape` read of a reversed word for `BufferWords` (the
   brief notes that none exists).
4. The phase-host glue `sl_rewrap`, `sl_guard` and `sl_tagged_ne_done` has siblings in other files
   (`b2b_dispatch_retag` in `Inclusions`, `record_tag_ne` in `CfgRecord`). Low priority.

**What this unblocks.**
- R (`NDCodeSimulator`'s `exists_ndInterpreterCore`), filled in parallel against this statement.
- U2-S's continuation (`UniversalK.exists_selfStartupTMK`). The closure (17 modules upstream) is
  free of `Build/StepBlock`, `CodeSimulator`, `UniversalK` and `NDCodeSimulator`, so U2-S can
  import the module (out/35-forbidden).
- B5a's H1.
- No file at the tip cites the target yet (out/41). After landing, the 94-module order list goes
  from 35 sorry warnings to 34, and `Build/SeamLayout` has none.
- The megafills issued at `6cfee544` (R's `c1-fill-core-cont2`, U2-S's `u2s-fill-startup-cont1`,
  and three others whose base sorry sets list it) cite the target as "sorried at your base"
  (out/45). Landing does not change their statement or their base. When their deliveries are
  reviewed after this lands, the seam layout's `sorryAx` drops out of their targets' closures at
  the landing tip.

## (e) Duplication and lint

| # | Check | Result | Evidence |
|---|---|---|---|
| 29 | Screen v3 script | SHA-256 `f4feac91…f181`, the same at base and head | out/28 |
| 30 | Before (base, the brief's 9-file population) | `867 declarations; 1112 pairs; 406,659 chars` (335 s). Byte-equal to the recorded base (`c1-fill-seamlayout-screen-base.txt`, the brief's MEASURED figures) and to the worker's `screen-before.txt` (comment and `rc` lines aside) | out/29, out/32-screens-compare |
| 31 | After (head) | `897; 1143; 431,082 chars` (377 s); equal to the worker's `screen-after.txt` | out/30, out/32-screens-compare |
| 32 | New pairs (`pairdiff.py`, by name) | 31 new, 0 gone. **0 cross-file**: every new pair has both sides in `SeamLayout.lean`. The head screen has no pair at all between a `SeamLayout` declaration and another file. The set equals the worker's | out/32-pairdiff, out/32-screens-compare |
| 33 | Pairs at ≥ 90% (the brief's copy line) | none; the maximum is 89% (`sl_phase7`/`sl_phase2`, the two skip-back instantiations). The families are as REPORT §8 lists and justifies them: 26 among `sl_phase1`–`sl_phase8` (the shared hosted-run scaffold), 4 among the step lemmas `sl_step_move`, `sl_split_step_true`, `sl_split_step_exit` (82–87%), and `sl_read_unary`/`sl_read_table` (54%). "New copies: none" holds | out/32-pairdiff |
| 34 | Known hazards, by name | no pair of an `sl_` declaration with `StepBlock` (its word identities, its phase key and instances), `UniversalStartup` or `Primitives` (`pairExtractTM` against `sl_pairSkipTM`) | out/32-screens-compare |
| 35 | Commit 6 (screen) | Before commit 6, `sl_apply_eq`'s bulleted `apply Cfg.ext` proof paired at 63% with `Primitives`' `pairExtractTM_fst_run`. The shared text was the generic idiom of applied-action field equations, not a duplicated argument. Commit 6 restates the proof fieldwise, and REPORT §8 discloses this. The real sibling of `sl_apply_eq` is `ExhaustiveReplay`'s `xr_act_apply`, which is outside the population and landed after the base (promotion candidate 2) | out/05, `patches/0006-*` |

| # | Check | Result | Evidence |
|---|---|---|---|
| 36 | Lint, `TuringMachine/Build` | base `0 FAIL, 30 WARN over 38 files`; head `0 FAIL, 31 WARN`. The new WARN is the file size (1,755 > 1000), which is not a driver (ground rule 8). Equal to the worker's `lint-after.log` | out/34 |
| 37 | Proof sketches (policy §3) | 36 declarations, all with a docstring. 15 proofs exceed 20 non-blank lines; 14 of them (all private) have no "Proof sketch" (F3). The target's sketch describes the proof the code performs | out/49 |

## (f) Environment (addendum v2.3)

| Item | Recorded | Evidence |
|---|---|---|
| Preflight (02:06 UTC) | `nproc` 4. cgroup v1 with no limit (`9223372036854771712`), so the headroom is `MemAvailable` = 15,871,524 kB = 15.14 GiB ≥ 4 GiB: PASS. The REPORT's `memory.stat` numbers match the log. Disk 24.56 GiB free ≥ 12 GiB (ext4, `/dev/vda`); the re-check after the toolchain install was 22.15 GiB ≥ 8 GiB | `logs/preflight.log`, out/37 |
| Toolchain | elan installed `leanprover/lean4:v4.25.0` (`cdd38ac5`). Part 2's shim was not needed | `logs/toolchain-install.log` |
| Cache command | `TAR_OPTIONS=--no-same-owner lake exe cache get $(cat …/mathlib-roots.txt)` (as REPORT quotes it; the log holds the output only) | REPORT §2 |
| Roots | 40, byte-equal to my computation from the order list at the head (base + the (a0) import) | out/36-mathlib-roots-review.txt, out/37 |
| Files fetched | 1,002/1,002, 0 failed, "Completed successfully", unpacked in 3,967 ms. No retry (item 4) | `logs/cache-get.log`, out/37 |
| Manifest check (item 2) | 11 packages `url OK rev OK`. `doc-gen4`, `UnicodeBasic`, `BibtexQuery` and `MD4Lean` show `url MISMATCH rev MISMATCH` with empty values, and the log ends `MANIFEST CHECK: FAIL`. These are the documentation toolchain, which the narrowed fetch does not clone, so they are absent rather than at another pin. REPORT's reading is right in substance (F4.4). **For the addendum:** v2.3's narrowed fetch makes item 2's "check each one" fail by construction; v2.4 should say "each package present in `.lake/packages`" | `logs/manifest-check.log` |
| Item 3 | the probe `import Mathlib.Algebra.BigOperators.Fin` (the first root) gave an empty log (REPORT: exit 0) | `probes/CacheProbe.lean`, `logs/cache-probe.log` |
| Bootstrap (item 5) | the full 94-module list once, up front, in order: 94/94 exit 0; 35 sorry warnings in 15 modules = the base list, by name | out/31 |
| Item 6 | `/usr/bin/time -v` was unavailable, so start and end times were logged but not memory. No stall, no exit 135/137/139, no `oom`, no E-RES | out/37 |
| Bans | no `lake build` and no unfiltered `lake exe cache get` in any log or in REPORT | out/37 |

## (g) Landability

- **The owned file is unchanged from the base to the tip** (blob `d0af5ae6` at both). The series
  applies cleanly at `2ff214c5` and gives the head blob `483be51b` (out/36, out/39).
- **Upstream.** The module's 17-module upstream closure (with `BufferWords`) is the same at the
  head and at the tip. All 17 blobs are unchanged from the base to the tip, and none of #133, #134,
  #136, #137 or #138 touches it (out/36, out/38-up-tip). So `oleans-lbw2` is the right snapshot for
  the owned module.
- **Elaboration at the tip.** `wt-tip` against `oleans-lbw2`: exit 0, no diagnostics (out/40).
- **The facade's environment.** I inlined the head module into a file with all 72 of the facade's
  imports except `Build/SeamLayout`. Against `oleans-lbw2`: 0 diagnostics, so no new name clashes
  with any facade module at the base (out/42). At the tip and at #139's and #143's heads, no other
  file declares `sl_Key`, `sl_PairPhase`, `sl_SplitPhase` or the derived instance names (out/41).
- **Replay closure at the tip** (`g5x-closure.py` over the tip's imports, out/38):
  `Build/SeamLayout` and the `TuringMachine` facade, 2 modules. The root `TCSlib` is not listed.
  - No olean snapshot matches the tip's TCSlib tree `268944d6`. The candidates are `oleans-lwpa`
    = `1cd66f1b`'s `0fdc787d` (without #137) and `oleans-l137b` = `fb6210b7`'s `f8925645`
    (without #133, #134, #136 and #138).
  - The facade's replay therefore needs a merged-tree replay, unless the maintainer already has a
    snapshot of the tip. From `oleans-lbw2`, the closure of every file changed from the base to the
    tip, plus this landing, is **13 modules**, listed in out/38-merged-replay. Do not compose
    snapshots.
- **Overlap with the open PRs' closures** (out/43):
  - **#139** (`Build/StepClock`): 9 modules.
  - **#143** (`Build/ZoneRebalance`): 2 modules.
  - Each shares exactly one module with this landing, the `TuringMachine` facade, and neither
    contains `Build/SeamLayout`. Whichever lands second re-elaborates the facade against the
    other's result.
  - **#144** (`ExhaustiveReplay`, docstrings only): 4 modules (`ClassNP`, `Diagonalization`),
    no overlap.
- **Expected after landing:** `Build/SeamLayout` 0 sorry warnings, the facade 0. The order list
  goes 35 → 34 (out/31).

## (h) Recommendation

**Not yet clear to merge**: the landing PR has not been opened, replayed or gated yet. It is clear
once that PR's replay passes and its gate is recorded.

**Land (full): yes**, by a maintainer PR into `complexity/arora-barak-ch3-4`.
- **Commits.** Squash the 6 commits `d6dd89ab..09773a66` from the verified bundle into one (their
  prerequisite is `1c06ea94`; they touch only the owned file, which is unchanged at the tip). Give
  it a public-facing subject, e.g. "SeamLayout: the seam layout proved", and drop the
  `Claude-Session:` trailer (F5).
- **Maintainer edits, docstring-only, in the same PR:**
  1. `Build/SeamLayout.lean` line 27: "`Turing.exists_seamLayoutTM` — the redistribution's
     contract (sorried)." → "… (proved)."
  2. The facade `TuringMachine.lean`, tip line 176: "the one redistribution the step-block
     startups cite. Sorried." → "… Proved." (the tip's `Build/Rewind` style).
  3. Optional, frozen text (the user's call): the target's docstring ends (head line 1485) with
     "Fill obligations, named: the two leaves' framed contracts; …", a campaign status sentence
     that is now discharged. Drop it, or reword it as "The proof's ingredients: …".
  4. Optional (F2): explicit `private instance`s instead of the three `deriving` clauses.

  Both files are in the 2-module replay closure. Line widths stay ≤ 100 characters.
- **Replay:** the 2 modules into a snapshot of the tip, or the 13-module merged-tree replay from
  a copy of `oleans-lbw2` (out/38-merged-replay). Expected: 0 failures, with `Build/SeamLayout` and
  the facade at 0 sorry warnings. If #139 or #143 lands first, replay into its result.
- **Review table for the PR body:**
  - integrity (33/33 sums, bundle, 6 commits, patch = bundle = file);
  - scope (regions (a0), (a), (b); statement and docstring byte-identical; 35 `sl_` privates; one
    import);
  - elaboration at the base and at the tip (0 diagnostics);
  - axioms (standard three, no `sorryAx`);
  - seals S1/S2 with controls;
  - F1 (the phase-8 self-redirect; equal tables);
  - probes 45/45 and 110/110;
  - edge cases run;
  - screen 867 → 897 declarations, 1,112 → 1,143 pairs, 0 cross-file;
  - lint 0 FAIL;
  - sweep 94/94, 35 → 34.

**Decisions for the user:**
1. **F1: accept the phase-8 self-redirect.** Recommended: yes. The brief's route needs an
   unpublished table fact, and the delivered machine's table equals the brief's.
   - Separately, should the phase host get a published last-phase lemma or table equation
     (promotion candidate 1)? That would avoid the same gap in later briefs.
2. **F3: proof sketches for the 14 long private proofs.** Either land now and record the debt for
   the docstring pass, as for C1-E, or add sketches in the landing PR. I suggest landing now, since
   R and U2-S's continuation are waiting, with sketches later at least for `sl_unarySplit_copy`,
   `sl_pairSkipTM_run`, `sl_phase6` and `sl_phase8`.
3. **F2: the derived public instance names.** Accept per precedent (`xr_St`, `wl_Phase`), or ask
   for explicit private instances (edit 4).
4. **Dedup** (the maintainer's window, not this landing): one public applied-action normal form
   for `sl_apply_eq` and `xr_act_apply`, and a reverse read for `BufferWords` (promotion candidates
   2 and 3).
