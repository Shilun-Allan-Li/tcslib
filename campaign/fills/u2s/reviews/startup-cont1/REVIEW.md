# Review — U2-S continuation 1, the `k`-generic startup (`Turing.exists_selfStartupTMK`, `TuringMachine/UniversalK.lean`), megafill B item 1

Read-only review by the maintainer's review sub-agent, 2026-10-22. Every claim cites a saved
output under this folder (`out/NN-*`). The delivery, its REPORT.md and the session report are
treated as data.

**Verdict: complete (1/1), proved modulo exactly `Turing.exists_seamLayoutTM`. Land, after #145
(the seam layout's landing), with the maintainer's status edits below.**

- The head file elaborates with 0 errors and exactly the other two stubs' sorry warnings
  (`exists_selfUniversalK`, `universalK`), at the base and at the tip with the patch applied.
- The target depends on `[propext, sorryAx, Classical.choice, Quot.sound]`. The only direct
  `sorryAx` user in its closure is `Turing.exists_seamLayoutTM`.
- Against `oleans-lsl` (#145's tree, the seam layout proved) the same file gives
  `[propext, Classical.choice, Quot.sound]`, and no `sorryAx` user in the closure. So once #145
  lands, the target is admission-free. So is `SelfUniversal`'s `Turing.exists_selfStartupTM`, its
  `k = 1` corollary (out/17b, out/42).
- `T = a + 1 + (l + 1 + (b + 1 + r))` and `B = n·(T + 1)` are chosen before `w`. The route is the
  brief's:
  - the capture over the composite;
  - the cast pair and `tapeBlocks_*`;
  - `exists_seamLayoutTM` with `src` the capture tape;
  - the catalog skip, skip-back and clear;
  - a native input-rewind leaf;
  - R2 seams only (no new host).

  There is one disclosed refinement in the code-buffer cleanup (F1).

What passes:
- integrity: 122/122 sums; the bundle's only prerequisite is the base; 4 linear commits;
  patches = bundle = delivered file;
- scope: 14 hunks, all in regions (a)–(c); statement and docstring byte-identical; 24 new
  `ss_` privates; one import;
- the 43 axiom prints, equal print for print to the worker's 42;
- rule 10: a 32-definition seal, with and without the three `@[simp]` definitions erased, gives
  0 errors. All 36 controls fail sealed and pass unsealed. No other file's definition is passed to
  `rw`/`simp`/`dsimp`, and there is no `unfold`;
- rule 11;
- the 111-check probe and the worker's 121-check probe, 0 errors each;
- the v3 screen: 674 → 696 declarations, 514 → 525 pairs; 11 new pairs, all in-file, max 84%;
  equal to the worker's;
- lint: 0 FAIL; the one new WARN is the file size;
- the worker's 95-module sweep: 33 → 32 sorry warnings, every other module unchanged by name.

Findings (none blocks landing):
- **F1 (route, decision: accept).** The brief's step 5 reads "skip, then skip back; at −1, one
  step right; clear". The delivery does: skip; a conditional one-step leaf; a second skip; skip
  back; the same leaf as an empty-code origin correction; clear (head 599–1174).
  - The leaf `ss_bufferLeaf` is one `tapeAction` that moves the tested head only when its cell is
    blank. It is read through the public `step_of_tapeAction_move`. No public row makes a single
    (conditional) step. Ground rule 7 names only the input-rewind leaf as allowed, but this leaf is
    none of the banned kinds (host, seam, embedding, parser, layout machine).
  - The correction is forced. For `α = []` the buffer is all blank, and its head at `p − 1 ∈ {−1, 0}`
    cannot be located by any machine. The brief's "at −1, one step right" cannot be executed
    there.
  - The machine therefore carries one parameter of `E`: `p [] ≤ 1`, the cleaned canonizer's final
    virtual input position on the empty code, chosen before `α` and `w`. It already depends on `E`
    through its canonizer (as in round 1, gate 48). The statement (`∀ E, ∃ R`) allows this, but it
    refines the gate guidance's "the control varies with `k` alone", which literally fits H2-F
    (gate 26).
  - REPORT discloses both points.
- **F2 (scope, minor; precedent).** `deriving DecidableEq, Fintype` on the private
  `ss_RewindState` generates two public instance names: `Turing.instDecidableEqSs_RewindState`
  and `Turing.instFintypeSs_RewindState`, with their `_proof_*` (out/15b). No clash at the tip,
  #145, #144, F5 or G4 (out/41). This is the seam layout's F2 case ("no ruling needed").
- **F3 (records, minor).** Where REPORT is inaccurate:
  1. Its "121 names" are 121 checks of 118 names; 3 of the 10 added checks repeat issued names
     (out/25).
  2. The probe misses 4 public lemmas the new code cites: `FinTM.bufferTape_left`,
     `FinTM.moveInputPos_neg_val`, `MultiTapeTM.runFrom_zero` and `Cfg.ext`. All are public at
     the base (out/25b).
  3. The worker's seal control is a single `bufferedCompTM` control in a separate file. Mine has
     36 (out/19b).
  4. The checkpoint zips cp1–cp3 are not in this delivery. Only their REPORTs and probes are under
     `evidence/u2s/`.
- **F4 (environment, note).** The queue's narrowed cache fetch downloaded only 35 of the 1,002
  archives it unpacked, so 967 were already in the host's Mathlib archive store before the
  session's first Lake command (out/37, `cache-get.log`). REPORT calls the 35 "missing files" but
  does not say where the 967 came from. It does not affect this review, since every check here was
  re-run on the maintainer's host. For addendum v2.5: log the archive store's state before the
  fetch.
- **F5 (dedup, the maintainer's window).** In-file only:
  - the three framed seam joins `ss_bufferSeek_run`, `ss_bufferFinish_run` and
    `ss_bufferCleanup_run` share one scaffold (80–84%);
  - their `hm` state-map equalities restate `ss_live_map` (51%).

  One private seam adapter would remove about 150 lines. Promotion candidates are in (d).

## Inputs

| Input | Identity | Evidence |
|---|---|---|
| Outer zip `exchange/inbox/megafill-b-delivery.zip` | SHA-256 `14f6193f…1307e` (as given). 6 members, each byte-equal to `inbox-megaB/zip/`; CRC OK | out/01, out/02 |
| Item zip `fill-u2s-startup-cont1.zip` | `95a0e169…1dbdd4` (as given and as the session report says). 123 members, each byte-equal to the extraction; no unsafe entry | out/01, out/02 |
| `SHA256SUMS` | 122/122 OK; covers every member except itself | out/03 |
| Brief, dispatch copy `exchange/outbox/fills/u2s-fill-startup-cont1.md` | `cf425d47…6d2b96` (as given). It is the base's (= records') `campaign/fills/u2s/briefs/u2s-fill-startup-cont1.md` (`dd8ff5c6…`) with its three `@ANCESTOR@` := the base | out/07 |
| Cover brief `megafill-B.md`, addendum v2.4 | outbox = base = records (the addendum is `42555a4f…`). The worker's attachment log records the same five hashes | out/07, `attachment-verification.log` |
| Brief inputs | overlay (`b0d18336`), 111-check probe, 13-file population, 95-module order list, base sorries, screen base, pre-ship log: base blobs = records blobs | out/07 |
| Base `6cfee54474e3d954e3395f9d9eab5d025452a8dd` | records commit; TCSlib = `2ff214c5`'s (#137's merge) | out/36b |
| Head `8e1aee0fc57a54b26678355396bda5922f71a49e` | the bundle's only ref `refs/heads/fill/u2s-startup-cont1`; fetched into `refs/review/u2s-cont1` | out/04 |
| Snapshots | `oleans-lg4c2` (`c60ed898`'s tree); `oleans-lsl` (the seam layout's landing at `7cd01f84`, proved; the maintainer's replay, 14/14) | out/36b, out/17 |
| Campaign tip | `git fetch` failed (github.com:443 unreachable, out/44). The local refs, updated by the maintainer's pushes, moved during the review, from `b7447492` to `34af2e0f`. That commit is records-only: its TCSlib tree `2babcaec` is `b7447492`'s. #145 = `lean/c1-seamlayout-fill` at `126127b8`, the merge of the campaign branch into `7cd01f84`. Its Lean diff from the tip is SeamLayout (`05d4e353`) and the facade (`a2d44457`). #144 = `lean/c1-exhaustive-sketches` (`0beb75a3`) | out/44, out/44b |

**The snapshot.** `oleans-lg4c2` differs from the base in the facade, `Build/InputWindow` and
`Build/ZoneRebalance`. None of these is upstream of `UniversalK`. All 50 upstream modules have the
same blob at `lg4c2`'s tree, at the base and at the tip (out/36b). So `lg4c2` is exact for the
owned module at the base and at the tip, and the axiom walk needs no correction.

**Review worktrees**, all detached under this folder, each with the `.lake/packages` link:
- `wt-base` (base) and `wt-ovl` (the base with the overlay);
- `wt-head` (head) and `wt-patch` (the base with the series `git apply`'d);
- `wt-tip` (`b7447492` + the series) and `wt-tip0` (`b7447492`);
- `wt-merged` (`b7447492` + #145's two files + the series + the drafted status edits; its TCSlib
  = `126127b8`'s apart from those two files, out/44b).

Lean ran only through `tools/leanelab.sh`, one elaboration at a time; there was no build or cache
command. The screens ran under `nice -n 10`, each started only when no screen was running.
Probe and seal sources are in `probe/`, scripts in `scripts/`. No delivered C or Python file was
run.

## (a) Integrity and scope

| # | Check | Result | Evidence |
|---|---|---|---|
| 1 | Bundle | `verify` okay. One ref = `8e1aee0f` (REPORT's final commit). Its sole prerequisite is the base | out/04 |
| 2 | Commits | 4, linear, no merges; first parent the base. Each touches only `UniversalK.lean`; in all +1186/−23. Author `Codex <codex@openai.com>`, as round 1. Subjects are descriptive, with no trailers. Times 05:24–06:07Z, inside the item's 05:14–06:14Z window | out/05 |
| 3 | First commit `51a8c643` | Carries the only import change in the series: `import TCSlib.Complexity.TuringMachine.Build.SeamLayout` after line 10. Head lines 1–159 = the overlay's. The bootstrap ran at the overlay (UniversalK sorries at 500/545/583) | out/05b, out/31 |
| 4 | Patch series | the 4 patches applied at the base give the head blob `8deea7d8`. Each equals `git format-patch` of its commit up to full `index` hashes and the git-version trailer | out/06 |
| 5 | Delivered file | = the head blob (SHA-256 `2f273f14…`) | out/06 |
| 6 | Regions | 14 hunks. (a) the import. (b) 12 hunks inside the home, base lines 159–469 (`/-! ## U2-S: the startup -/` up to the target's docstring). (c) base line 513, `  sorry` → 249 lines. (d) is unused (complete). Byte-identical: the target's docstring and statement (base 470–512 = head 1385–1427), the module header apart from the import, and everything from `/-! ## U2-U` on | out/09 |
| 7 | Freeze (`declfreeze.py … exists_selfStartupTMK`) | public 12 → 12, none added or removed; the target is an "authorized body change". Private 15 → 39: 24 added, 0 removed, 3 restated (`ss_captureInitial`, `ss_capture_indices` (their sketches), `ss_capturedPrefix_run` (over the composite)) | out/10 |
| 8 | Hygiene (1186 added lines, code only) | no `sorry`, `admit`, `axiom`, `unfold`, `delta`, `set_option`, `open`, `section`, `variable`, `attribute`, `decide`, `native_decide`, `noncomputable`, macro/elab or `#eval`. No unrestricted `simp`/`simpa`/`dsimp`, and no `simp_all`, `aesop` or `norm_num` anywhere in the file | out/11, out/20b |
| 9 | Widths (characters) | no line of the file over 100 characters; the widest added line is 96 | out/11 |
| 10 | Size | 590 → 1,753 lines; 12 public / 39 private (lint INFO) | out/34 |
| 11 | Generated public names | the two derived instances (F2) and the target's `_proof_1_*` auxiliaries; nothing else | out/15b |
| 12 | Public-facing text | the 100 added comment/docstring lines have no campaign label, path, date or session word. They use library terms ("catalog row", "published equations", "public seam") | out/35-public-text |
| 13 | Other stubs | `exists_selfUniversalK` and `universalK` keep their `sorry` (head 1707, 1745) | out/13 |

**The 24 new private declarations** (head lines). Roles are as in REPORT's tables; all bodies
were read.
- *Phase 2:*
  - `ss_tapeBlocks_zeroLeft` (405): the composite's block partition with the parser's empty
    left block;
  - `ss_prefix_return_fields` (436): the prefix run's fields through the cast pair;
  - `ss_capturedPrefix_fields` (505): the normalized return, with `t` and `p ≤ |α| + 1` chosen
    before `w`.
- *Phase 3:*
  - `ss_serialized_layout` (564): `exists_seamLayoutTM` at `serializeK M`, by `serializeK_eq`
    and `unaryFin_eq`;
  - `ss_bufferLeaf`/`_run` (599, 611);
  - `ss_bufferSkip_run` (635);
  - `ss_bufferAdvance`/`_run` (680, 691);
  - `ss_bufferSeek`/`_run` (798, 808);
  - `ss_bufferBack_run` (882);
  - `ss_bufferClear`/`_run` (912, 924);
  - `ss_bufferFinish`/`_run` (1009, 1018);
  - `ss_bufferCleanup`/`_run` (1087, 1100).
- *Phase 4:*
  - `ss_RewindState` (1177), `ss_inputRewind` (1182), `ss_inputRewind_done` (1196) and
    `ss_inputRewind_run` (1221);
  - `ss_live_map` (1298) and `ss_block_updates` (1315).

## (b) Elaboration and axioms

| # | Check | Result | Evidence |
|---|---|---|---|
| 14 | Base file, `oleans-lg4c2` | exit 0; sorry at 499, 544, 582 (the pre-ship's 500/545/583 minus the import line) | out/12 |
| 15 | Head file, `oleans-lg4c2` | exit 0; **only** `1707:8` and `1745:8` `declaration uses 'sorry'` (U2-U, U2-E). REPORT says the same | out/13 |
| 16 | Axioms: an in-module copy with 43 prints (39 privates, the 3 targets, `exists_seamLayoutTM`), an admission walk and a dependency walk | target `[propext, sorryAx, Classical.choice, Quot.sound]`. Direct `sorryAx` users in its closure: **`[Turing.exists_seamLayoutTM]` only**. `ss_serialized_layout` `[propext, sorryAx, Quot.sound]`, through the same constant. The other 38 privates are within the standard three (24 / 5 `propext, Quot.sound` / 1 `Quot.sound` / 8 none). The other two targets are each their own sole `sorryAx` source | out/15, out/16 |
| 17 | Against the worker's `phase4-final-check3.log` | 42 common prints, **none differs** (mine adds `exists_seamLayoutTM`) | out/16b |
| 18 | **After #145** (the same copy against `oleans-lsl`, whose 51 upstream modules of `UniversalK` are blob-equal to the merged tree's) | target **`[propext, Classical.choice, Quot.sound]`**; direct `sorryAx` users in its closure: `[]`. `exists_seamLayoutTM` and `ss_serialized_layout` are standard too. The merged-tree file itself elaborates with the same 2 warnings | out/17, out/17b, out/17c, out/38-up-merged-vs-lsl, out/40b |
| 19 | The `k = 1` corollary after #145 (UniversalK + SelfUniversal inlined, `oleans-lsl`) | `Turing.exists_selfStartupTM` **`[propext, Classical.choice, Quot.sound]`**. `exists_selfUniversal` keeps U2-U's `sorryAx` | out/42 |
| 20 | Other files' privates reached | one, `_private…UniversalStartup…universalPrefix_start._proof_1`, inside the **public statements** of `prefixCanon_run`/`_start` (round 1's row 18). No other | out/16 |
| 21 | Equation/unfolding lemmas reached | only `FinTM.rewind_scan.match_1`, the matcher in `rewind_scan`'s and `rewind_heads`'s hypothesis `hscan` (a statement, not an unfolding) | out/16, Simulation.lean 538–580 |
| 22 | TCSlib constants reached (target + 39 privates) | 134: 67 theorems, 32 semireducible definitions, 12 projections, 6 instances, 8 constructors, 7 inductives, 1 matcher, 1 reducible (`Cfg.Halted`). None from `Build/InputDevice`, so the item does not depend on F5 | out/18, out/18b, out/17d |

## (c) Correctness, route and rule 10

**The construction** (head 1428–1676). Let `G := bufferedCompTM universalPrefixTM
(ss_cleanCanonizer E.canonizer)`, `n := (G.k + 1) + (k + 2)` and `K := G.k + 1`.
- The source block is `ss_sourceSlot` (tapes `k + 2 …`), with the capture tape `k + 2 + G.k`;
  the code buffer is `ι 0 = k + 2`, `tbl = k`, `sm = k + 1`.
- The machine is `W := seamCompTM A (inr ()) (seamCompTM L done (seamCompTM J jexit
  (ss_inputRewind n) .enter) (inl jentry)) (inl entry)`, where:
  - `A` is the restarted returning capture of round 1;
  - `L` is the seam layout's machine at `(n, cap, tbl, sm)`;
  - `J := ss_bufferCleanup n code (p [])`.
- The exit is the rewind leaf's `.done`.
- `G.k > 0` holds by `bufferedCompTM_k` and `universalPrefixTM_k`, so a canonizer with no work
  tapes is covered. No hypothesis restricts `k`, `E`, `α` or `w`.

The theorem's correctness rests on the kernel-checked proof (rows 15–18). I read every new body.

| Item (brief route) | Status | Notes |
|---|---|---|
| 1. Two sketches | **done** | `ss_captureInitial`, `ss_capture_indices` (out/49) |
| 2. Capture over the composite | **as briefed** | `ss_capturedPrefix_run`'s `ι : Fin (bufferedCompTM universalPrefixTM (ss_cleanCanonizer F)).k ↪ Fin n`; `prefixCanonTM_eq` is rewritten in `ss_prefix_first_halt` before the capture, so there is no dependent rewrite under `ι` |
| 3. Normalized return | **as briefed** | `bufferedSecondCfg_workTapes_cast`/`_workTapePos_cast` + `tapeBlocks_buffer`/`_right` (via `ss_tapeBlocks_zeroLeft`); `embedSilentCfg_selected_*`, `_cap`, `_unselected`, `_inputPos`. The code buffer holds `bufferTape α` with its head at `p − 1`, `p ≤ |α| + 1` (the cleaned canonizer's input position, chosen before `w`); the cleaned block is blank with heads 0; the capture tape holds `serializeK (E.machine α)` with its head at its length; the input head is at `2|α| + 3`; the output is `[]` by silence |
| 4. Redistribution | **as briefed** | `exists_seamLayoutTM n cap tbl sm` with `r = |s|`. Its `T` is obtained per `E.machine α` before the configuration (`hL (E.machine α)` before `intro w`). Its endpoint is the target's tapes `k`/`k + 1` by `serializeK_eq`, `unaryFin_eq`; `src` is cleared; the three heads are 0; input position and output are unchanged |
| 5. Code-buffer clear | **refined (F1), accept** | skip (`v + 1`); leaf-left + skip (`w₀ + 3`); skip back (`|α| + 3`); leaf with the fixed `p []` move + clear (`2|α| + 4`); the internal seams make `b = v + w₀ + 3|α| + 14`. Every case is covered: head at −1 (`p = 0`), on the right blank (`p = |α| + 1`), and `α = []` with `p [] ∈ {0, 1}`. Each step is a catalog `_run_ofCfg` or the leaf's one-step contract, joined by `seamCompTM_run_ofCfg`/`_firstReturn_ofCfg` |
| 6. Rewind, fresh exit | **as briefed** | a four-state `FinTM.controlAction` leaf (`enter, scan, stop, done`) read through `rewind_scan` and `rewind_heads`. It takes `inputPos + 2 = 2|α| + 5` steps exactly, keeps the work heads fixed and reaches the input head at 1. The exit `.done` is reached first at `T` (the stationary `ss_inputRewind_done` excludes an earlier one). Optional simplification: `rewind_scan_heads` gives the heads directly, without identifying `rewind_heads`' existential `r` |
| 7. `T`, `B`, silence, first exit | **as briefed** | `T = a + 1 + (l + 1 + (b + 1 + r))`, with `a = 3|α| + 4 + t α` and the three outer dispatches. `refine ⟨T, n * (T + 1), ?_⟩` comes before `intro w`. `B` is by `spaceUsed_le_mul_succ`. Silence holds for all `u ≤ T` by `output_prefix` and the final `[]`; the first exit by the inherited first-return cuts. No regularity assumption on `E.canonizerTime` |
| Joins | **as briefed** | R2's `seamCompTM` throughout; no `phaseHostTM`, no new host, seam, embedding, parser or layout machine; no `UniversalStartup`/`SeamLayout` private |
| Adversarial instances | **covered** | `k = 0`, `w = []`, a canonizer with no work tapes, `α = []` and the buffer head at −1 are all instances of the proved universal statement. The proof treats `α = []` and `p = 0` explicitly (F1) |

**Rule 10.**

| # | Check | Result | Evidence |
|---|---|---|---|
| 23 | Seal set | the 32 other-file, semireducible, non-projection, non-instance definitions reached by the target and the 39 privates. This is **the worker's `seal-final.txt` exactly**, and it contains round 1's 21 | out/18b, out/18c |
| 24 | Seal S1 (the whole `namespace Turing` body in a section, the 32 `local irreducible`) | **0 errors**; the 2 out-of-scope sorry warnings only | out/19-U2SSealHead |
| 25 | Seal S2 (S1 + `attribute [-simp]` on `Action.apply`, `Cfg.init`, `MultiTapeTM.initCfg`, the three `@[simp]` definitions reached) | **0 errors**, 2 warnings | out/19-U2SSealSimpHead |
| 26 | Controls (18 at the section's top, 18 at its end: `runFrom`, `bufferTape`, `mapState`, `skipTM`, `skipBackTM`, `clearTM`, `pairEncode`, `seamCompTM`, `initCfg`, `Cfg.init`, `controlAction`, `tapeAction`, `bufferedCompTM`, `embedSilentCfg`, `workTapeSymbols`, `unaryFin` by `rfl`; `Action.apply` and `initCfg` by `simp`) | unsealed: 0 errors. Sealed with the body (S2): exactly **36 errors, one per control, none in the body** | out/19-U2SControlUnsealed, out/19-U2SSealControl, out/19-U2SSealSimpHeadCtl, out/19b |
| 27 | The worker's `SealFinal.lean` (head + the 32-name block at file level, read) | 0 errors, 2 warnings | out/19-worker-seal |
| 28 | `rw`/`simp`/`simpa`/`dsimp` arguments (whole file: 556 occurrences, 161 identifiers) | 41 TCSlib theorems (published field equations, the cast pair, `tapeBlocks_*`, `serializeK_eq`, `unaryFin_eq`, `controlAction_apply`, `moveInputPos_*`, run/step equations); 5 own declarations; 115 local hypotheses/lets and core/Mathlib lemmas. **No other file's definition** | out/20 |
| 29 | `change`/`show`/`rfl` (11/4/55 in the added lines) | Each `change` exposes a local let, a projection of a local anonymous constructor, or the file's own tables (`ss_inputRewind` at `.enter`/`.stop`/`.done`, `ss_bufferLeaf`). The `rfl`s close own-table equations, `Option.map` on `some`, and `Fin`/cast identities. All pass under S1/S2 | out/11, head 1201, 1235, 1257, 1518–1546 |

**Rule 11.**
- No R3 row token and no R3 row among the reached constants.
- No other file's private (beyond row 20's statement auxiliary).
- The token hits are spelling collisions with public names (`Cfg.mapState_state`,
  `FinTM.moveInputPos_neg_val`) or prose.
- Every new private is `ss_` (out/27).

## (d) Escalations and promotion candidates

**Escalations: none, and I agree.** Every fact about another file is read through a public
lemma (rows 23–29), so there is no API gap. F1 needed no escalation: the worker resolved the
brief's under-determined `α = []` case inside the brief's rules and disclosed it.

**Import probes (check 5).**

| # | Probe | Result | Evidence |
|---|---|---|---|
| 30 | The brief's `U2SCont1ImportProbe` (111 checks; the delivered `evidence/u2s/ImportProbe.lean` is byte-equal) | 0 errors; the stand-in module's 3 sorry warnings. Its output equals the first part of the 121-check output | out/24, out/24-summary |
| 31 | The worker's `ImportProbeFinal.lean` (the 111 verbatim + 10 checks) | 0 errors. Output = the worker's `final-import-probe-121.log`, paths aside | out/24 |
| 32 | Citations outside the 121 | 57 reached constants. All but 8 are structural (constructors, inductives, projections, instances, the matcher) or sealed definitions read through the probed lemmas. The 8 theorems: 4 cited by new code (`FinTM.bufferTape_left`, `FinTM.moveInputPos_neg_val`, `MultiTapeTM.runFrom_zero`, `Cfg.ext`; public at the base, F3); 3 round-1 citations (`exists_first_halt`, `runFrom_of_halt`, `runFrom_state_ne_none_of_le`); and `instInhabitedCfg.default._proof_1`, an instance's auxiliary. No post-base or private citation | out/25, out/25b |

**Promotion candidates.** REPORT names two, conditionally: the conditional one-step leaf and the
live-map adapter. For the maintainer's window, roughly by expected payback:
1. **`ss_tapeBlocks_zeroLeft`**: the buffered composite's blocks when the first machine has no
   work tapes (`universalPrefixTM`). UN's setup reads the same composite (round 1's F1 "Shared").
   It is a one-lemma addition beside `tapeBlocks_*` in `Simulation`.
2. **`ss_serialized_layout`**: the seam layout at a source `serializeK M`. R (`NDCodeSimulator`,
   megafill A) cites the same contract. Its home must import both `Build/SeamLayout` and
   `CodeSimulator`; SeamLayout's own closure has neither (seam review, (d)).
3. **`ss_inputRewind` + `_run`**: a native input rewind with an exact time and a fresh exit (what
   `rewind_heads` leaves existential).
4. **`ss_bufferLeaf` + `_run`**: a conditional one-step catalog row.
5. **`ss_live_map`**: a public `Cfg.mapState` normal form at a live state, in `Configuration`.

## (e) Duplication and lint

| # | Check | Result | Evidence |
|---|---|---|---|
| 33 | Screen script | `f4feac91…f181` at the base, head and tip | out/28 |
| 34 | Before (the overlay, the 13-file population) | `674 declarations; 514 pairs; 151,065 chars` (141 s). = the recorded base (the brief's MEASURED) = the worker's `screen-before.txt` | out/29, out/32-screens-compare |
| 35 | After (head) | `696; 525; 162,136 chars` (155 s). = the worker's `screen-final.txt` and `screen-final-verified.txt` | out/30, out/32-screens-compare |
| 36 | New pairs (`pairdiff.py`, by name) | 11 new, 0 gone; **0 cross-file**; the set equals the worker's | out/32-pairdiff, out/32-pairdiff-worker |
| 37 | ≥ 90% | none. Max 84% (`ss_bufferSeek_run`/`ss_bufferFinish_run`) | out/32 |
| 38 | Known hazards | no pair between a `UniversalK` declaration and any other file. No `ss_` pair with `UniversalStartup` (`universalCanonTM`, `universalCaptureTM`), `UniversalInterpreter`, `NTimeHierarchy` (UN's capture), `NDCodeSimulator` (R's) or `SeamLayout` | out/32-screens-compare |

**The 11 pairs, justified.**
- **Seek/finish/cleanup (6 pairs, 56–84%).** Three framed joins share the same scaffold:
  - the first contract, then `a`;
  - `b := a.mapState _`, with its three field facts and the second contract;
  - `hm`;
  - `seamCompTM_run_ofCfg` and `_firstReturn_ofCfg`;
  - the time arithmetic and the final `Cfg.ext`.

  The machines and contracts differ, so these are not copies. A shared adapter is F5's dedup
  point.
- **Two more scaffold pairs.** `ss_bufferAdvance_run`/`ss_bufferClear_run` (50%) share the
  leaf-then-row scaffold. `…Finish_run`/`…Cleanup_run` against `ss_live_map` (51%) restate that
  lemma in their `hm` blocks.
- **`ss_capturedPrefix_fields`/`_run` (56%).** The shared statement prefix.
- **`ss_inputRewind_run`/`_done` (55%).** The run invokes `_done`; the step computation is
  shared.
- **"New copies: none" holds.**

| # | Check | Result | Evidence |
|---|---|---|---|
| 39 | Lint, `TCSlib/Complexity/TuringMachine` | base `0 FAIL, 63 WARN over 82 files`; head `0 FAIL, 64 WARN`. The one new WARN is the file size (1,753 > 1000), which is not a driver (ground rule 8). The merged tree with #145: `0 FAIL, 66 WARN`, the tip's 64 plus the two size WARNs | out/34, out/50c, out/50d |
| 40 | Proof sketches | every new or changed proof over 20 lines has a literal "Proof sketch". The target's frozen sketch matches the proof in substance; it names `FinTM.timed_rewind`, whereas the proof reads `rewind_scan`/`rewind_heads` | out/49 |

## (f) Environment (addendum v2.4, shared with the session)

| Item | Recorded | Evidence |
|---|---|---|
| Preflight (05:10Z) | 9 CPUs; overlay filesystem; 23,909,351,424 bytes free (22.27 GiB ≥ 12); `memory.max` 8,589,934,592; `anon + kernel + shmem` = 100,847,616 + 193,372,160 + 0 = 294,219,776; headroom 8,295,714,816 (7.73 GiB ≥ 4); `oom` = `oom_kill` = 0. `max 85641` is reclaim, not a shortage (item 1). Page cache excluded as required. All equal to REPORT and the session report | `evidence/logs/preflight.log`, `preflight-summary.json` |
| Re-check before the cache | 19,655,630,848 bytes ≥ 8 GiB | `pre-cache-disk.log` |
| Part 2 | the condition occurred (`error: failed to locate application`). The shim source is SHA-256 `985924ad…4fba7`, **byte-equal to the addendum's block**. No `.so` shipped. `LD_PRELOAD`, `LEAN_SYSROOT`, `LAKE_HOME` are recorded and scoped to Lean/Lake. Lean 4.25.0 `cdd38ac5` started with the shim | out/37, `lean-start.log`, `lean-shim-start.log` |
| Cache (Part 3, item 2) | union order list = this item's 95 modules (as sets); **40 roots, byte-equal to my computation** at the overlay. Exit 0; 35 downloads, 1,002 unpacked, 0 failed, no retry; 0 empty oleans; the root probe passed. 11 packages URL+rev PASS; the four doc packages absent (the narrowed fetch, as the seam review's F4.4 noted) | out/37, `cache-get.log`, `package-verification.log`, `cache-probe.log` |
| F4 | 967 of the 1,002 archives were present before the first Lake command; their origin is unrecorded | `cache-get.log` |
| Bootstrap (item 3.2) | 95/95 in the order list's order, exit 0; 33 sorry warnings in 14 modules = the base set, by name; at the overlay (UniversalK 500/545/583); 505 s summed; peak 2,927,084 KiB | out/31 |
| Final sweep | 95/95 in order, exit 0, no error; **32 in 14**. Every module equals the base set by name except UniversalK (3 → 2, `exists_selfStartupTMK` gone). 520.325 s summed, peak 2,939,516 KiB, as REPORT says. UniversalK was checked at 06:13:20Z, after the final commit (06:07:13Z) | out/31 |
| Item 6 | `/usr/bin/time` absent; `wait4` start/end and max RSS recorded instead | REPORT, `final-sweep.log` |
| Bans | no `lake build`, no unfiltered `lake exe cache get` in any log | logs |

## (g) Landability

- **The owned file is unchanged from the base to the tip**: blob `50123141` at the base,
  `b7447492`, `34af2e0f`, #145 (`7cd01f84`/`126127b8`) and #144 (out/36-tip-changes, out/44).
  The tip's Lean changes since the base are #139 (`Build/StepClock`) and #143
  (`Build/ZoneRebalance`). Neither is upstream of `UniversalK` (out/35-upstream, out/36b).
- **At the tip.** The series applies cleanly at `b7447492` (= `34af2e0f`'s TCSlib) and gives the
  head blob. Against `oleans-lg4c2`, which is exact for the 50 upstream modules: exit 0 with the
  2 warnings (out/39, out/40).
- **Imports.** At the base, the import adds exactly `Build/SeamLayout` to the closure (49 → 50).
  After #145, `BufferWords` (SeamLayout's new import) joins as well (51). Neither closure contains
  `UniversalK` (out/35-upstream, out/38-up-merged).
- **This landing's own replay closure** (`g5x-closure.py`, root excluded): `UniversalK`,
  `SelfUniversal`, `TuringMachine` (3 modules, out/38-down-tip).
- **Merged-tree replay** (the campaign's method; no snapshot matches the tip). The closure of
  every `.lean` file changed since `e9e97970`, in the tree tip + #145 + this landing, is
  **17 modules** from `oleans-l132b` (out/38-merged-replay). The list is **identical, order
  included, to the maintainer's current `fills/replay/down-lsl.txt`**, #145's own rebased list
  (out/43). So:
  - if #145 lands with a replay of its merged tree (`126127b8`), this landing needs only its
    3 modules, replayed into a copy of that snapshot;
  - otherwise it needs the 17 modules from `l132b`.

  Do not compose snapshots.
- **Overlaps.**
  - **#145:** the facade, and `UniversalK` itself, which becomes downstream of SeamLayout. The
    facade edits are different hunks (line 176 against 248), and the two PRs touch no other
    common file.
  - **#144** (`ExhaustiveReplay`, docstrings): its own closure (ExhaustiveReplay, ClassNP,
    NTimeHierarchy, Diagonalization) is disjoint from this landing's (out/43). It shares modules
    only through the merged-tree lists, as every current landing does.
- **F5** (`Build/InputDevice`, upstream) is independent: no InputDevice constant is reached
  (row 22). F5's landing replays `UniversalK` downstream. The canonizer's cont7
  (`CodeSimulator`, upstream) likewise.
- **Name clashes:** none (F2, out/41).
- **Expected after landing (with #145):**
  - UniversalK: 2 sorry warnings;
  - SelfUniversal and the facade: 0;
  - the 95-module order list: 33 → 31 (SeamLayout's and U2-S's);
  - `exists_selfStartupTMK` and `exists_selfStartupTM`: `[propext, Classical.choice,
    Quot.sound]` (rows 18–19).

## (h) Recommendation

**Not yet clear to merge.** The landing PR is not open yet, not replayed and not gated, and #145,
on which it should sit, has not merged. It becomes clear once #145 has merged, the landing PR's
base is the campaign branch (not stacked), its replay has passed and its fill gate is recorded.

**Land (full): yes**, by a maintainer PR into `complexity/arora-barak-ch3-4`, **after #145**.
- **Order.** Land #145 first, so that U2-S lands admission-free (row 18). Landing before #145 is
  sound, but the target would carry the seam layout's `sorryAx` until then.
- **Commits.** Cherry-pick the 4 commits `51a8c643..8e1aee0f` from `refs/review/u2s-cont1`
  (prerequisite `6cfee544`; they touch only the owned file, unchanged at the tip), or squash
  them. Their messages are already public-facing. Branch from the tip after #145, or retarget
  before "clear to merge". Link `.lake/packages` in the PR worktree.
- **Maintainer edits, docstring-only, in the same PR** (drafted and checked: out/50; widths ≤ 100
  characters; UniversalK elaborates with the 2 warnings, out/50b):
  1. `UniversalK.lean` lines 29–31, the stale status. Replace "**Status: statement gate pending**
     (`audits/u2-statements-pack.md`). … the three machine contracts are sorried …" with
     "**Status.** The scheme interface and its two instances are defined and proved, and so is
     the startup `Turing.exists_selfStartupTMK`; the other two machine contracts are sorried with
     their proof sketches." This also drops an `audits/` path from rewritten text.
  2. `UniversalK.lean` line 63: "… (sorried)." → "… (proved)."
  3. The facade `TuringMachine.lean` line 248: "evaluator. Statement gate passed 2026-10-15; the
     three contracts are sorried." → "evaluator. The startup is proved; the other two contracts
     are sorried." The dated ruling leaves the rewritten sentence.
  4. Optional: in the target's frozen sketch, "(`Turing.FinTM.timed_rewind`, `2|α| + 5` steps)"
     → "(`Turing.FinTM.rewind_heads`, …)" (row 40). Optional too: explicit `private instance`s
     instead of `deriving` (F2).
- **Replay:** see (g). Expected: 0 failures; UniversalK 2 sorry warnings, SelfUniversal and the
  facade 0.
- **Review table for the PR body:**
  - integrity: 122/122 sums, bundle, 4 commits, patches = bundle = file;
  - scope: regions (a)–(c), statement and docstring byte-identical, 24 `ss_` privates, one import;
  - elaboration at the base and at the tip: the 2 out-of-scope warnings;
  - axioms: `sorryAx` only via the seam layout, standard after #145;
  - the S1/S2 seals with 36 controls; F1; probes 111/121;
  - screen 674 → 696 declarations, 514 → 525 pairs, 0 cross-file;
  - lint 0 FAIL; sweep 95/95, 33 → 32.

**What remains in the file:**
- `exists_selfUniversalK` (U2-U): the proved startup, then a seam into H2-F's
  `exists_forwardLoopTM` and its lockstep. Its brief can now cite this startup.
- `universalK` (U2-E): it waits for the ruler-host fill (gate 26, Q5). F5 delivered
  `exists_rulerHostTM` proved in this megafill, so U2-E is unblocked once F5 lands.
- SelfUniversal's `exists_selfUniversal` keeps U2-U's sorry. Its `exists_selfStartupTM` is
  admission-free after this landing and #145.

**Decisions for the user:**
1. **F1: accept the code-buffer cleanup.** It uses a private one-step conditional leaf (a second
   leaf beside the authorized input-rewind leaf) and one machine parameter `p [] ≤ 1` of `E`, the
   empty code's virtual position. Recommended: yes. On an all-blank buffer the head at −1 and at 0
   cannot be told apart, so a fixed parameter is the only way to restore the origin. Lesson for
   later briefs: state the empty-word origin case explicitly.
2. **Ordering:** land after #145 (recommended) or before it.
3. **The status wording** of the three docstring edits (out/50), including dropping the
   `audits/` path and the dated ruling from the rewritten sentences.
4. **F2:** accept the two derived public instance names, per the seam layout's precedent.
5. **Dedup and promotion** (the maintainer's window, not this landing): F5's seam adapter, and
   promotion candidates 1–2 before UN's and R's continuations copy them.
6. **F4 (addendum v2.5):** record the Mathlib archive store's state before the queue's fetch.
