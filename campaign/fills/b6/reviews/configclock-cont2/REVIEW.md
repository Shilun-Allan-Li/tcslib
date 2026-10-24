# Review — B6 F3, continuation 2: the configuration-count runner (`Turing.exists_configWindowRunnerTM`, `SpaceComplexity/WindowClock.lean`), delivery `fill-b6-configclock-cont2.zip`

Read-only review by the maintainer's review sub-agent, 2026-10-24 (UTC). Every claim cites a saved
output under this folder (`out/NN-*`). The delivery, its REPORT.md, logs, probes and tools are
treated as data; nothing from the zip was run except the worker's Lean probes, copied into my
worktree after a scan (out/23).

**Verdict: complete (1/1), with no admission. Land, by a maintainer PR, with the two status-text
edits drafted below (F1), after the user's decisions on the route refinements (F2) and the
landing order against #156 (F6).** Nothing blocks the mathematics:
- The delivered file elaborates with **0 errors and no diagnostic at all**, at the base (out/11),
  and on both of #156's trees, `a4d9b024` and `0e5f210b` (out/37, out/37b). A copy with the ledger's constant weakened fails in the
  time bound, so the run is real (out/11b).
- `Turing.exists_configWindowRunnerTM` depends on `[propext, Classical.choice, Quot.sound]`; its
  sorry-source walk is empty. All 70 declarations of the module are within the standard three;
  the prints equal the worker's `axioms.log` (out/13, out/19).
- The construction is Route A over field cells: `c = C₂ + |Q| + 8` passes, `W = c · F ≤ c · L`,
  one phase host for the writer, F2's runner, the clear and the exits; the statement's constant is
  `C = (14c + 13) + 4c + 0 + 10 + C₂(c + 1) + c + 2`, as REPORT §6 says.

What passes:
- integrity: 82/82 internal sums; the bundle's only prerequisite is the base; six linear commits,
  each touching only the owned file; the six patches = `format-patch` of the bundle's commits and
  reproduce the delivered file (blob `71327d9d`, SHA-256 `316fcd69…`) at the base and at the tip;
- scope: every hunk in regions (a)–(c); imports unchanged; public 4 → 4 at source, no statement
  changed; 55 new `cw_` privates, two restated (`cw_copy_constant`, `cw_clear_patch`), none removed;
  new public constants only of workflow.md §4's two kinds, with no name clash (out/14, out/14b);
- rule 10: my 34-definition seal (the worker's 32 plus the two derived `Fintype` instances): the
  body has 0 errors; 34/34 `rfl` controls close unsealed and fail sealed, each with exactly one
  error. No other-file TCSlib definition and no core/Mathlib definition is passed to `rw`, `simp`,
  `dsimp` or `unfold`. Rule 11: no R3 row, no external private;
- probes: the brief's import probe (102) and consumer probe standalone, the worker's 145-check probe,
  join probe, seal controls and module copies, and both probes appended to the head module: all as
  expected, and byte-equal (paths aside) to the worker's and the pre-ship's outputs (out/25);
- lint 0 FAIL (81 → 82 WARN; the new one is the file size); the worker's 182-module final sweep
  28 → 27, exactly the base set minus the target;
- the v3 screen: 1,058 → 1,102 declarations, 513 → 521 pairs; 8 new, all in-file, none ≥ 90%
  (highest 88%), no cross-file pair, none removed; identical to the worker's after-screen.

Findings (none blocks the mathematics):
- **F1 (landing edit, minor).** The module's **Status** paragraph and its "Main results" entry,
  frozen for the worker, still call the target "sorried". Drafted and checked (A1, A2).
- **F2 (route refinements; decision, accept recommended).** One phase host carries the rounds (the
  brief's checkpoint 1 says "by `seamCompTM`"); the three exits are a stationary leaf phase
  (`.stop`); the certification comes from F2's own last clause, not `windowRun_stop_unique`.
- **F3 (duplication, note).** Eight new in-file pairs, the highest 88% (`cw_seg_back` ⟶
  `cw_seg_skipS`); none cross-file, none ≥ 90%. All justified; no semantic re-derivation of
  published API.
- **F4 (rule-10 records, note).** The worker left the two derived `Fintype` instances out of its
  seal because its `isDefEq` controls did not bite; concrete `rfl` controls do bite, and the body
  passes with them sealed. Its `seal-test.log` records only the exit status.
- **F5 (records, minor).** The five checkpoint zips are not in the inbox; the commit subjects carry
  campaign labels; three double blank lines; the status paragraph names four private lemmas.
- **F6 (landing order, decision).** WindowClock's closure lies inside #156's, WindowClock itself
  included, not only the facade. #156 moved to `0e5f210b` during this review; that head also
  changes `Build/WindowRun`, upstream of WindowClock. Its round-2 replay `lphl2` passed (23/23)
  during this review; gate 69's round 2 is pending.

## Inputs

| Input | Identity | Evidence |
|---|---|---|
| Zip `exchange/inbox/fill-b6-configclock-cont2.zip` | SHA-256 `076cea1a…19732e5` (as given); 94 entries (83 files), no unsafe name or symlink, CRC OK; copied to `delivery/` and extracted there; every member byte-equal to the extraction | out/01 |
| `SHA256SUMS` | 82/82 OK; covers every member except itself | out/01 |
| Brief (dispatch copy) `exchange/outbox/fills/b6-fill-configclock-cont2.md` | SHA-256 `f0294fba…6c66d` (as given, and as REPORT says); equal to the repository copy except the two `@ANCESTOR@` lines | out/44 |
| Addendum `campaign/standards/fill-environment-addendum.md` | v2.5, SHA-256 `90851511…3abf0` at base and tip, as REPORT says | out/44 |
| Brief inputs | import, join, route and consumer probes, population (21 files), order list (182), base sorry set (28 in 11), screen base (1,058 / 513) and pre-ship log: the base copies equal the tip's; the `inputs/` import probe equals `preship-906a9d7b/`'s | out/24 |
| Base `968d7b2bfbcd9635d8a763673731c89f1a125eda` | a records commit; TCSlib tree `f2c39238` = #155's merge `906a9d7b`'s = the campaign tip `6e8db28f`'s; `git diff --name-only` on `*.lean` empty both ways; owned blob `b50cdbb1` at all three | out/02 |
| Head `ebca0bc53382464f7ff674909e8ac3aa5fb673e6` | the bundle's only ref, fetched into a scratch clone (`scratch-clone/`, `refs/review/f3c2`; the main repository's refs untouched) | out/03, out/04 |
| Snapshots | `oleans-lslsk` (exactly the base's Lean content); `oleans-lphl` (#156's first head `a4d9b024`, 88/88) and `oleans-lphl2` (#156's round-2 head `0e5f210b`, 23/23, chained from `lphl`) | out/10, out/37, out/37b |
| Campaign tip | `6e8db28f` (= `wt-hk`) at the start; **`aad8a095` from about 05:12Z** (two records commits: gate 69 round 1, the `lphl2` replay); no Lean file changed, WindowClock's blob still `b50cdbb1`. Open PRs: #156 `lean/phasehost-last` (`a4d9b024` at 04:43Z, **`0e5f210b` from 04:53Z**), #135 (chapter 7, into `main`) | out/15, out/46 |

Review worktrees, all detached under this folder, each with the `.lake/packages` link (checked
absent first):
- `wt-base` (the base), `wt-head` (the base with the delivered file), `wt-tip` (the tip with the
  delivered file), `wt-land` (the tip with the delivered file and the drafted landing edits).

A first attempt under zsh created three worktrees at mistaken paths (the main checkout's HEAD);
nothing was copied or elaborated in them, and they were removed cleanly (out/06). Lean ran only
through `tools/leanelab.sh` (`scripts/elab.sh`), one elaboration at a time; no build or cache
command was run. The screen ran once, niced, while holding `locks/screen.lock` (`scripts/screen.sh`).
Probe and seal sources are in `probe/`, scripts in `scripts/`.

## (a) Integrity and scope

| # | Check | Result | Evidence |
|---|---|---|---|
| 1 | Bundle | `verify` okay; one ref `refs/heads/fill/b6-configclock-cont2` = `ebca0bc5`; sole prerequisite the base `968d7b2b`. Equal to the worker's `bundle-verify.log` | out/03 |
| 2 | Commits | 6, linear, first parent the base; author `fill-agent <ragavanbsco@mit.edu>`; 00:42:25Z–00:43:19Z (recommitted after the work, REPORT's "History note"); each +/− only in the owned file (+708/−36, +61/−8, +162/−8, +36/−7, +54/−1, +288/−27). The list equals REPORT §1's | out/04 |
| 3 | Patches | the six apply in order at the base and reproduce the delivered file byte for byte; each equals `git format-patch` of its commit up to the git-version trailer | out/05 |
| 4 | Delivered file | = the head blob `71327d9d` (SHA-256 `316fcd69…`); `git diff --check` clean | out/04 |
| 5 | Regions | 10 hunks, all in (a) the home (base 287–359), (c) the status paragraph (base 404–424 → head 1492–1505) and (b) the body (base 456 → head 1537–1678); 0 outside. Equal to the worker's `regions.log` (41 lines removed, 1,263 added) | out/09 |
| 6 | Freeze (`declfreeze`) | public 4 → 4, none added or removed; the target's change is its body and status paragraph (authorized, regions (b) and (c)); without the authorization the same change is reported as the only one | out/07 |
| 7 | Privates (`declfreeze`, `privstmt`) | 11 → 66: 55 added; **changed: `cw_copy_constant`, `cw_clear_patch`**; removed none. `privstmt` reports no statement change because its parser stops at the first `:=` (`{ d with state := … }`); the manual comparison: `cw_copy_constant`'s endpoint becomes the constant `wordPatch`, and both gain their row's cut and head-range clauses (region (a) allows it). The other nine are byte-identical | out/07, out/08, out/08b |
| 8 | Code lines (`stmtcheck`, `codeonly`) | 15 base code lines not found in order, all inside the two restated helpers and the target's `sorry`; code differs (expected) | out/08 |
| 9 | Imports | unchanged (`Build/WindowRun`, `SpaceComplexity/ConfigGraph`) | out/44 |
| 10 | Public constants (workflow.md §4) | 8 → 118 non-private names: 13 `exists_configWindowRunnerTM._proof_1_N` auxiliaries, and the derived `Turing.instDecidableEqCw_Idx` and `Turing.instFintypeCw_Idx` (with 95 auxiliaries) of the private inductive `cw_Idx`; **no other**. No name clash in the tree at the tip, at #156's or #135's head | out/14, out/14b |
| 11 | Hygiene (1,263 added lines, 1,050 code lines) | no `sorry`, `admit`, `axiom`, `set_option`, `open`, `section`, `variable`, `attribute`, macro, syntax, `native_decide`, `delta` or `#` command; one `deriving DecidableEq, Fintype` (row 10); two `private instance`s; one `decide` (`Nat.pow_le_pow_right (by decide)`, a core `Nat` fact); six `unfold`s, all of own definitions; 18 `show`s and 5 `change`s (row 27) | out/45, out/21 |
| 12 | Widths, whitespace | widest added line 99 characters (file max 99); no trailing whitespace or tab; three double blank lines (head 566, 831, 1315; F5) | out/29, out/40 |
| 13 | Rule 11 | R3 rows: none. Token hits `S`, `T`, `one`, `sum`, `trans`, `mapState_state` are type variables, prose, `List.sum`, `.trans` and the public `Cfg.mapState_state`. No external private in any declaration's elaborated closure (row 18). All 55 new privates are `cw_` | out/22, out/13 |
| 14 | Size | 458 → 1,680 lines; 4 public / 66 private (lint INFO) | out/28 |

**The 55 new privates** (head lines): the patch facts `cw_patch_rep` (290), `cw_buffer_rep` (299),
`cw_join` (309); the host `cw_Idx` (432), `cw_Ctrl` (455), `cw_Ctrl_fintype` (468),
`cw_Ctrl_decidableEq` (475), `cw_rows` (481), `cw_next` (495), `cw_prev` (502), `cw_afterSkip` (512),
`cw_red` (520), `cw_hostTM` (543); the writer's configurations `cw_cfg` (551), `cw_zero_ne_last`,
`cw_cfg_clockTape`, `cw_cfg_clock`, `cw_cfg_tape`, `cw_cfg_pos₀`, `cw_cfg_posL`, `cw_cfg_pos`,
`cw_mapState_pos`, `cw_mapState_tapes`, `cw_mapState_io`, `cw_cfg_mapState`, `cw_cfg_pos_zero`,
`cw_cfg_zero`, `cw_cfg_move₀`, `cw_cfg_moveL` (561–680); the head box `cw_box`, `cw_box_of`,
`cw_box_row`, `cw_cfg_box` (700–739); the segments `cw_guard` (756), `cw_seg` (769), `cw_seg_row`
(799), `cw_seg_copy`, `cw_seg_skipS`, `cw_skip_word`, `cw_seg_skipC`, `cw_seg_left`, `cw_seg_time`
(837–977); the writer `cw_field` (983), `cw_round` (1000), `cw_pass` (1037), `cw_seg_back` (1086),
`cw_rewind` (1112), `cw_pass_rewind` (1156), `cw_passes` (1183), `cw_seg_clockBack` (1239),
`cw_silence` (1267), `cw_writer` (1284); the runner and the end `cw_seg_run` (1319), `cw_seg_clear`
(1341), `cw_finish` (1438). REPORT §4's table lists exactly these, with accurate roles.

## (b) Elaboration and axioms

| # | Check | Result | Evidence |
|---|---|---|---|
| 15 | Base file, `oleans-lslsk` | exit 0; `426:8` `declaration uses 'sorry'` only (the brief's pre-ship) | out/10 |
| 16 | Head file, `oleans-lslsk` | exit 0; **no diagnostic at all** | out/11 |
| 17 | Sanity | the head with `A := nc` (instead of `14 nc + 13`) fails at 1659 (`unsolved goals`, the time bound) | out/11b |
| 18 | Axioms: an in-module copy with 70 prints, a sorry-source walk per declaration, an external-dependency walk and a public-constant listing | target `[propext, Classical.choice, Quot.sound]`; every walk empty; of the 70, 36 use all three, 17 `propext, Quot.sound`, 6 `propext`, 2 `Quot.sound`, 9 none. No external private, no external equation or unfolding lemma (`List.IsPrefix.eq_of_length` matches the name filter only: a Mathlib theorem). At the base the target is `[propext, sorryAx, …]` with itself the only source | out/13 |
| 19 | Against the worker | the 70 prints equal `axioms.log` by name; the worker's axiom and seal copies are the delivered module plus prints / plus the seal lines only | out/19, out/18 |
| 20 | TCSlib constants reached (the 66 privates and the target) | 99: 44 definitions (27 semireducible non-projection, 5 derived instances, the rest projections or reducible auxiliaries), 37 theorems, 8 inductives, 10 constructors. No reached definition is `@[simp]`. Equal, as sets, to the worker's `defs-used.log` (99 cited, 44 definitions) | out/16, out/41 |
| 21 | Each checkpoint commit's file (cp1–cp5) | exit 0; only the target's sorry warning (1098, 1151, 1305, 1334, 1387), as the worker's `cp/` logs say. The series is bisectable | out/30 |
| 22 | Head file on #156's trees | `oleans-lphl` (`a4d9b024`): exit 0, no diagnostic; `oleans-lphl2` (`0e5f210b`, with the re-proved `wr_prefix` in `Build/WindowRun`): exit 0, no diagnostic | out/37, out/37b |

**Downstream consumers.** No Lean declaration anywhere uses the target: only docstrings name it
(WindowClock's header, `Build/WindowRun`'s module text), at the tip and on #156's and #135's heads.
Neither the brief ("proved modulo: none") nor REPORT claims that a downstream admission goes away;
`Complexity.space_hierarchy` stays sorried (out/26).

## (c) Correctness, route and rule 10

I read every new body. Correctness rests on the kernel-checked proof (rows 16–18).

**The construction.** `cw_hostTM e R en ex c m := phaseHostTM (cw_rows e R) ⟨.stop, .exhausted⟩
(cw_red en ex)` on `K + 2` tapes (F2's), with phases `copy p j`, `skipS p j`, `skipC (some (p, j))`,
`left p j` (one field's round), `back p j` (the record's rewind), `skipC none` and `clockBack` (the
clock's return), `run` (F2's runner `R₂`), `clear b` and `stop`. Every phase is one framed row
(`copyMapTM` with the constant merge on tape `0 → Fin.last (K + 1)`, `skipTM`, `skipBackTM`,
`clearTM`), the landed leaf `cw_leftTM`, `R₂`, or the stationary exit leaf. Every phase is read
through `phaseHostTM_run` (`cw_seg`), and segments compose by the public `Segment.trans`. The writer's
configurations are one family `cw_cfg e d q a n b` (record head `+a`, clock head `+b`, `n` copies of
`e` patched at the clock's start), so the clock's blank suffix is carried by construction (the clock
is always a patch over the blank start tape).

| Item (the brief's route) | Status | Notes |
|---|---|---|
| 1. The per-field round | **refined (F2a)** | `cw_round`: copy (`2l + 2`), skip on the record (`l + 1`), skip on the clock (`l + 1`), one-cell move (`1`), each plus a dispatch: `4l + 9`. Four consecutive host phases, not a `seamCompTM` round machine. The write is joined to the earlier patch by `cw_join` (`wordPatch_append`); the copy's cut and head range come from the restated `cw_copy_constant` (the brief's option "extend the helper") |
| 2. One pass | **as briefed** | `cw_pass`, by induction on the fields left |
| 3. `c` passes with the record's rewind | **as briefed** | `cw_rewind` (`m` skips back, `l + 4` each), `cw_pass_rewind`, `cw_passes` (induction on the passes left); the clock ends as `wordPatch ct p (replicate (c · F) e)` |
| 4. The clock's rewind | **as briefed** | `skipC none` (the skip over the empty word at the clock's right delimiter, one step right) then `cw_seg_clockBack` (`skipBackTM` over the word) |
| 5. The writer's contract | **restated** | `cw_writer`: `∃ t ≤ 13 · c · fieldOffset fs \|fs\| + c · F + 6`, a segment avoiding the exits from `d` to the runner's entry configuration, every head within `r ≥ c(\|joinFields fs\| + 1) + 2`, silent. Explicit time; the endpoint is F2's entry itself |
| 6. The target | **as briefed, two refinements** | the writer on all tapes directly (an option the brief gives; no embedding); F2's runner at its entry; `cw_seg_clear` at `halted`/`left` with the blank exterior from the writer and `w'.length = W`; the exits as the `.stop` phase (F2b); certification `fun N hN hNe => hcert N hNe (hclock N hN)` from F2's own clause (F2c); `cw_time_bound` at `A = 14c + 13`, `D = 0`; `cw_head_bound`; space by `spaceUsed_le_of_abs_le` at `r = C(L + 1)` (`cw_finish`); silence by `output_prefix` (`cw_silence`) |
| Ledger (REPORT §6) | **matches the proof** | `t ≤ T_w + (t₂ + 1) + (2W + 3)` with `T_w ≤ 13c(L + 1) + W + 6` and `t₂ ≤ 5(2^W − 1) + 2W + 3`; then `cw_time_bound`; the constant `C = A + 4c + 0 + 10 + C₂(c + 1) + c + 2` (body, `hC`) |
| Edge cases | **covered** | `x = []`, `s = 0`, `M.k = 0` (three fields) and every `K`, `T` are instances of the universal statement; no hypothesis restricts them. The writer's lemmas hold for any field lengths, empty fields included (`cw_seg_left` needs only `1 ≤ n + \|f\| + 1`); it needs only `0 < c` and `0 < m`, both true (`c ≥ 8`, `m = k + 3`). Tape `0 ≠ Fin.last (K + 1)` for every `K` (`cw_zero_ne_last`). At `exhausted` no clear is claimed, as the statement asks |

**Rule 10.**

| # | Check | Result | Evidence |
|---|---|---|---|
| 23 | Seal set | the 27 semireducible non-projection definitions reached (`Cfg.InWindow`, `.inputSymbol`, `.mapState`, `.workTapeSymbols`, `FinTM.bufferTape`, `.configBound`, `MultiTapeTM.runFrom`, `.spaceUsed`, `.step`, `RecSym.digitEmb`, `RecordAt`, `Segment`, `cfgRecord`, `clearTM`, `copyMapTM`, `fieldOffset`, `fieldsTape`, `joinFields`, `moveInputPos`, `phaseHostTM`, `posWidth`, `recordLength`, `skipBackTM`, `skipTM`, `tapeAction`, `windowRun`, `wordPatch`), the five derived instances (`instDecidableEq{SeekPhase,SweepPhase,WindowExit}`, `instFintype{SeekPhase,SweepPhase}`), and the worker's two extras `MultiTapeTM.spaceUsedByTape`, `.visitedByTapeHead`: **34**. None is `@[simp]`, so no `[-simp]` erasure is needed. Not sealable locally: `FinTM.fintypeState` (a reducible instance projection), `WindowExit.casesOn`/`.ctorIdx` (generated, reducible) | out/16 |
| 24 | Seal (head line 142 `/-! ### The runner -/` to `end Turing` in a section, the 34 `local irreducible`, the 34 controls at the top of the section) | **34 errors, exactly one in each control, none outside**; the same module without the controls: **0 errors, 0 warnings** | out/17 (`F3C2RevSeal`, `F3C2RevSealBody`), `probe/` |
| 25 | Controls alone | unsealed: 34/34 close (0 errors); sealed: 34/34 fail, one error each | out/17 (`F3C2RevCtl*`) |
| 26 | The worker's seal (32 names) and controls, re-run here | the sealed copy: 0 errors, 0 warnings; `SealControls`: 31 × "unfolds", 31 × "sealed", and exactly its two `rfl` controls fail (97, 100); identical to its `seal-controls.log` (F4) | out/25 |
| 27 | `rw`/`rwa`/`simp`/`simp only`/`dsimp only`/`unfold`/`show`/`change` in the added lines | 220 calls, 313 rule elements, each identifier classified by Lean name resolution in the module's own context: 11 TCSlib theorems (`Cfg.mapState_output`, `Cfg.mapState_state`, `FinTM.bufferTape_nat`, `FinTM.bufferTape_of_neg`, `MultiTapeTM.runFrom_zero`, `fieldOffset_zero`, `joinFields_cfgRecord_length`, `length_joinFields_add_one`, `segment_iff`, `wordPatch_of_mem`, `wordPatch_of_not_mem`), 27 core/Mathlib theorems, 16 own theorems, 6 own definitions (`cw_Ctrl`, `cw_cfg`, `cw_hostTM`, `cw_next`, `cw_prev`, `cw_red`), locals. **No other-file TCSlib definition and no core/Mathlib definition is passed.** The six `unfold`s are `cw_hostTM`, `cw_next` (2), `cw_prev` (3). The 14 bare `simp`s close `cw_Idx`/`WindowExit` constructor disequalities, the three-element `Finset` membership and `\|0\| ≤ r`; the two bare `dsimp only` reduce projections of the file's own structure literals. `show`/`change` terms name `clearTM` (the landed `cw_clear_patch`'s `change`) and `Fin.last`; the seal covers any unfolding. Agrees with the worker's `rw-simp-args.log` | out/20, out/21 |

Pre-existing, not this delivery: the frozen bridge `FinTM.configBound_le_two_pow` unfolds
`FinTM.configBound`; it predates rule 10 and the seal starts after it.

## (d) Escalations, probes and promotion candidates

**Escalations: none, and I agree.** Every step closed from public lemmas (row 24). Route B was not
used.

| # | Probe | Result | Evidence |
|---|---|---|---|
| 28 | Brief's import probe (102 checks), standalone, `oleans-lslsk` | 0 errors, 0 warnings; identical to the pre-ship's `F3C2ImportProbe.out` | out/25 |
| 29 | Brief's consumer probe, standalone | 0 errors, 0 warnings; identical to the worker's `consumer-probe.log` and the pre-ship's | out/25 |
| 30 | Worker's import probe (145 = the 102 + 43), standalone | 0 errors, 0 warnings; identical to its `import-probe.log`. It covers all 99 constants reached; beyond the brief's list the proofs cite three published lemmas, `FinTM.bufferTape_of_neg`, `Segment.trans`, `segment_iff` (all public at the base) | out/25, out/42 |
| 31 | The 145 checks and the consumer probe, each appended to a copy of the head module | 0 errors, 0 warnings each | out/25 (`*OnHead`) |
| 32 | Worker's join probe (gate 56's published form) | exactly its two bare controls fail (48, 50); identical to its `join-probe.log` and the pre-ship's `F3C2JoinProbe-published.out` | out/25 |
| 33 | Worker's `MathlibProbe` | 0 errors | out/25 |
| 34 | Worker's `DefsUsed` | not re-run: it reads `TCSlib.Complexity.SpaceComplexity.WindowClock` from the environment, which needs the head's olean, and no snapshot has it. My in-module walk reproduces its output exactly (row 20) | out/41 |
| 35 | Scan of every delivered `.lean` before elaboration | no `#eval` with IO, `run_cmd`, `initialize`, `extern`/`implemented_by`, `native_decide`; the two meta probes only read the environment | out/23 |

**Promotion candidates** (REPORT's, my assessment): the clock writer (`cw_writer` with its host) as a
public "all-`e` word of width `c · F` at the clock head" row, and `cw_seg_row` (a framed one-head
row as a phase-host segment). The second is the more reusable: any phase host over catalog rows
needs it, and with #156's `phaseHostTM_run_le` a last-phase form would follow. Neither is needed now.

## (e) Duplication and lint

| # | Check | Result | Evidence |
|---|---|---|---|
| 36 | Screen v3 script | SHA-256 `f4feac91…f878f181` in `wt-head` and `wt-tip`, as REPORT says | out/44 |
| 37 | Before | the worker's `screen-before.txt` equals the recorded base `b6-fill-configclock-cont2-screen-base.txt` (1,058 declarations; 513 pairs; 149,070 chars) line for line, its timestamp, `commit:` and `exit:` lines aside | out/43 |
| 38 | After (my one run at the delivered head, `wt-head`, population `preship-906a9d7b/screen-population.txt`, 21 files) | `declarations screened: 1102; copy pairs …: 521; reproduced text: 150,388 chars`; exit 0, 716 s, niced, under the lock (held 04:58:59–05:10:55Z, released by the script's trap) | out/27 |
| 39 | New pairs (`pairdiff.py`, by name, against the recorded base and against the worker's before) | **8 new, 0 gone, all in-file** (WindowClock on both sides): `cw_seg_back` ⟶ `cw_seg_skipS` 88%, `cw_seg_clockBack` ⟶ `cw_seg_skipC` 79%, `cw_seg_skipS` ⟶ `cw_seg_back` 73%, `cw_cfg_moveL` ⟶ `cw_cfg_move₀` 69%, `cw_cfg_box` ⟶ `cw_cfg_pos_zero` 68%, `cw_prev` ⟶ `cw_next` 62%, `cw_red` ⟶ `cw_next` 61%, `cw_cfg_moveL` ⟶ `cw_cfg_pos_zero` 52%. **None ≥ 90%; no new cross-file pair.** The only cross-file pair naming WindowClock is the base's (`ConfigCount::ComputesInTime.of_spaceUsed_le` ⟶ the frozen bridge `FinTM.inWindow_of_spaceUsed_le`, 67%). No pair joins a `cw_` declaration with `rt_*`, `exists_fieldsCopyTM`, `wr_*`/`wl_*`, `embedEmit*` or `phaseHost*` (the brief's hazards) | out/43 |
| 40 | Against the worker | my after-screen equals its `screen-after.txt` line for line (metadata aside); its `screen-diff.txt` lists the same 8. REPORT §9's justifications are accurate, and its "new copies: none" holds | out/43 |
| 41 | Semantic re-derivations | none found. `wordPatch_append` (`cw_join`), `spaceUsed_le_of_abs_le` (`cw_finish`), `phaseHostTM_run` (`cw_seg`), `output_prefix` (`cw_silence`, the brief's prescribed `f3c2_silence` route) and `recordAt_iff`/`fieldsTape_field` (`cw_field`, the route probe's `f3c2_field`) are cited, not re-proved. No published lemma gives a phase-host phase as a `Segment`, a constant patch cell by cell, or a field of a record as a delimited word. `exists_fieldsCopyTM` copies the layout verbatim with its separators, so it cannot write the contiguous constant clock; the writer shares its shape (copy, skip, recurse, skip back), as the brief anticipated, and transcribes none of `rt_copyMachine` (row 39). The input head never moves, so `inputRewindTM` is not needed | out/34 |
| 42 | Lint, `SpaceComplexity` | base `0 FAIL, 81 WARN over 107 files`; head `0 FAIL, 82 WARN`; the new WARN is `WindowClock.lean 1680 lines > 1000` (size alone is no driver; ground rule 8). Byte-equal to the worker's `lint-base.log` and `lint.log` | out/28, out/28-lint-compare |
| 43 | Proof sketches, docstrings, public-facing text | all 55 new declarations have docstrings; the seven proofs over 20 lines (`cw_clear_patch`, `cw_seg_copy`, `cw_pass`, `cw_rewind`, `cw_passes`, `cw_seg_clear`, the target) carry a literal "Proof sketch". No campaign label, date, path or `sorry` in any added line. The status paragraph meets region (c)'s requirements: what is proved, the construction used (field cells, width `c · F`, field by field), and that the whole-layout alternative is not used | out/29 |

## (f) Environment (addendum v2.5, Part 1)

| Item | Recorded | Evidence |
|---|---|---|
| Preflight (23:29:34Z) | `nproc` 4; cgroup v1, limit 14,341,881,856 B; in use `usage − total_cache + total_shmem` = 40,574,976 B; headroom 13.32 GiB ≥ 4; `failcnt` 0, `oom_kill` 0; clone 24.51 GiB free ≥ 12, ext4; `/dev/shm` unused. The arithmetic checks. (The script reads `usage_in_bytes` twice, 64 KiB apart; REPORT quotes the computation's read.) Re-check before the cache: 22.10 GiB ≥ 8. **PASS** | `preflight.log`, `preflight-recheck.log` |
| Toolchain | Lean 4.25.0 (`cdd38ac5`), Lake 5.0.0; Part 2 not needed | `toolchain.log` |
| Store, roots, fetch | store absent before the fetch (0 files); **54 roots, byte-equal to my extraction from the order list and to the pre-ship's `roots.txt`**; "Attempting to download 1025", "Decompressing 1025", "Completed successfully!", exit 0; no failed download, `M − N = 0` | out/33 |
| Bans | no `lake build` and no unfiltered `lake exe cache get` in any log or tool; 1,025 files confirm the narrowed fetch | out/33 |
| Manifest | 11 present packages, each URL and revision equal to the base's `lake-manifest.json`; absent exactly `doc-gen4`, `UnicodeBasic`, `BibtexQuery`, `MD4Lean`; last line quoted in REPORT | out/33 |
| Cache checks | no zero-size olean; a probe importing the first root, rc 0 | `zero-oleans-check.log`, `cache-probe.log` |
| Bootstrap (at the base) | stage 1 = exactly the 60 order-list modules upstream of WindowClock, in list order; stage 2 = the other 122, in order (addendum item 5); WindowClock checked at the base separately (426:8 only). 182/182 rc 0, 0 errors; **28 sorry warnings in 11 modules = the base set**, by module and declaration | out/31, out/32 |
| Final sweep (00:43:31–01:07:41Z) | 182/182 in the list's exact order, rc 0, 0 errors; **27 in 10 = the base set minus the target**, by module and declaration; WindowClock with no diagnostic; all 436 diagnostics outside WindowClock identical to the bootstrap's | out/31 |
| Memory logging | every module's start, end, wall and child max RSS (`getrusage`; `/usr/bin/time` absent): peaks 2,890 / 2,591 / 2,813 MiB; longest module 125.5 s; nothing stalled | out/33 |
| Checkpoint zips | REPORT §11 names five; **not in the inbox** (F5). Their logs are in `evidence/logs/cp/`: each module check ran seconds before its commit, with only the target's sorry; my elaborations of the five commits agree (row 21) | out/30 |

## (g) Landability

- **The owned file is unchanged base → tip** (blob `b50cdbb1`). The six patches apply at the tip
  in a temporary index and give blob `71327d9d`, changing nothing else; the same on #156's
  current head `0e5f210b` (out/38).
- **Downstream closure at the tip** (`mkdownmulti.py`, `wt-tip`): `SpaceComplexity/WindowClock`,
  then the `SpaceComplexity` facade, **2 modules**; the root `TCSlib` is not in the list (out/35).
- **Overlap with #156** (out/36, out/15). #156's closure (everything downstream of `Build/Seam`,
  88 modules; the tip's import graph equals #156's, whose Lean changes keep their imports)
  **contains both modules of this landing: WindowClock itself, not only the facade.** WindowClock
  imports `Build/WindowRun`, which imports `Build/Seam`. During this review #156 was pushed to
  `0e5f210b` (gate 69's round-1 fix), which also changes `Build/WindowRun` (the `wr_prefix`
  proof), `Build/StepBlock`, `Build/OracleSim`, `SpaceComplexity/Inclusions` and `CodeSimulator`,
  all with their imports unchanged; its current closure is still 88 modules, WindowClock included.
  Its round-2 replay list (`down-lphl2.txt`, 23 modules, equal to the closure of the five round-2
  files) contains WindowClock too, and passed (23/23) during this review. There is no textual
  conflict: #156 never touches WindowClock, and this landing touches nothing else. #156 changes no
  statement that WindowClock cites (`phaseHostTM_run` keeps its statement; `exists_windowRunnerTM`
  is unchanged), and the delivered file elaborates on both of #156's trees (row 22). Whichever
  lands second re-elaborates WindowClock on the merged tree (F6).
- **The tip moved to `aad8a095`** during this review (records only; out/46): the patches still
  apply there, since WindowClock's blob and every Lean file are unchanged.
- **#135** (chapter 7, into `main`) is not on this branch's path.
- **Expected sorry count after landing:** the 182-module order list 28 → 27; WindowClock 1 → 0.

## Findings

**F1 (landing edit, minor).**
- *Claim:* the module docstring's **Status** paragraph (head 29–31) says the target "is sorried with
  its proof sketch", and "Main results" (head 44–45) lists it as "(sorried)". Both are outside the
  worker's regions ("the maintainer updates the module's status text at integration").
- *Evidence:* the head file; region map (out/09).
- *Resolution:* the drafted edits A1 and A2 (`scripts/landedits.py`, every replacement asserted;
  out/39):
  - A1: "**Status.** Everything here is proved: the bridges, and `Turing.exists_configWindowRunnerTM`,
    whose clock writer, phase host and clear are private to this module."
  - A2: "… configuration-count clock (proved)."
  - Checked on `wt-land` (the tip with the delivered file and A1, A2, B1–B3): elaboration with no
    diagnostic; code identical to the delivered file, comments stripped; `declfreeze`/`privstmt`:
    no declaration changed; lint 0 FAIL, 82 WARN; widest line 99 (out/40). Result blob `96a1d7b3`,
    SHA-256 `640645d5…`.

**F2 (route refinements; decision, accept recommended).**
- *Claim:* three departures from the route's wording, all disclosed in REPORT §5:
  - (a) the round is four consecutive phases of the one host, not a `seamCompTM` machine
    (checkpoint 1 says "by `seamCompTM`"). The brief's host rule lists the phase host among the
    combinators to compose by, and one host with pass and field indices avoids a seam inside each
    phase and its lockstep bookkeeping. No seam, host, loop or transport is written;
  - (b) the exits are a phase (`.stop`) whose machine is a stationary leaf
    (`⟨.exhausted, fun q _ _ => ⟨0, fun _ => (none, 0), none, some q⟩⟩`), written in this file.
    The brief allows `cw_leftTM` "and a one-step exit dispatch if a phase host needs one. Nothing
    else." `phaseHostTM_run` needs every finished phase redirected, so the exits need a phase of
    their own; this leaf is that phase's machine (it never moves, writes or halts), not a
    dispatch. It is the allowance's purpose, in a different form;
  - (c) the certification is F2's own last clause at each `N ≤ configBound + 1` (`cw_record_clock`
    supplies the budget), so `Turing.windowRun_stop_unique` is not used.
- *Evidence:* (c) of this review; the body (head 1537–1678); `cw_rows` (head 481).
- *Resolution:* accept all three (decision 1). Each uses less than the route allows; none adds a
  public name or an admission. With #156's `phaseHostTM_run_le`, a later cleanup could make the
  runner's exits the host's last phase and drop the stationary leaf; not needed.

**F3 (duplication, note).**
- *Claim:* the eight new pairs of row 39 are all inside WindowClock and all below 90%. The 88% and
  73% pair (`cw_seg_back`/`cw_seg_skipS`) and the 79% pair (`cw_seg_clockBack`/`cw_seg_skipC`) are
  thin wrappers that feed one framed row's three clauses to the shared `cw_seg_row`; the
  `cw_cfg_*` pairs are mirror-image case splits on a head (record, clock, other); `cw_next`,
  `cw_prev`, `cw_red` share the dependent-pair syntax of the redirect targets. None reproduces a
  proof from another file, and row 41 finds no semantic re-derivation.
- *Evidence:* out/27, out/43, out/34.
- *Resolution:* accept as justified (the worker's table, REPORT §9, is accurate). Optional, in
  the maintainer's window: one direction-generic "record-tape skip as a segment" lemma would merge
  `cw_seg_back`/`cw_seg_skipS` (the 88% pair).

**F4 (rule-10 records, note).**
- *Claim:* REPORT §8 drops `instFintypeSweepPhase` and `instFintypeSeekPhase` from the seal
  "because their controls do not bite". That is a property of its control, `isDefEq c (value c)`
  at default transparency, not of the instances: a concrete `rfl` on `Finset.univ.card` closes
  unsealed and fails sealed for both, and the body passes with them sealed (rows 24–25). The seal is
  therefore complete for every semireducible definition reached. Separately, `seal-test.log`
  records only `exit: 0`, not Lean's (empty) output; the sealed source is shipped and reproduces
  here with no diagnostic.
- *Resolution:* none needed for landing. For later briefs: ask for one concrete `rfl` control per
  sealed definition and for the seal's full Lean output.

**F5 (records and cosmetics, minor).**
- (a) The five checkpoint zips named in REPORT §11 are not in the inbox; moot for a complete
  delivery, and each checkpoint commit elaborates here (row 21).
- (b) The commit subjects carry campaign labels ("(F3 cont2, checkpoint N)"); the author is
  `fill-agent <ragavanbsco@mit.edu>`. Not Lean text; see decision 3.
- (c) Three double blank lines (head 566, 831, 1315): optional edits B1–B3 (drafted with F1).
- (d) The status paragraph names four private declarations (`cw_record_clock`, `cw_hostTM`,
  `cw_time_bound`, `cw_head_bound`), as the base's paragraph did; fine to keep.

**F6 (landing order against #156; decision).**
- *Claim:* this landing's whole closure is inside #156's (section (g)); #156's head moved to
  `0e5f210b` during this review, adding `Build/WindowRun` (upstream of WindowClock) to its changes;
  `lphl2` has since passed, and the delivered file elaborates on it.
- *Evidence:* out/15, out/35, out/36, out/37, out/37b, out/46.
- *Resolution:* the options are in decision 4; either order costs a 2-module replay of WindowClock
  and the facade.

## Decisions for the user

1. **F2: accept the route refinements** (one host for the rounds; the stationary exit leaf; the
   certification from F2's own clause).
   - (a) **Recommended:** accept all three and record them; the leaf is the exits' phase that
     `phaseHostTM_run` forces, and it is the only leaf besides `cw_leftTM`.
   - (b) Accept (a) and (c), and ask a short continuation to replace the leaf, e.g. by making the
     exits the runner's own exit states through #156's `phaseHostTM_run_le` once #156 lands.
2. **F1 and F5c: the landing edits.** A1 and A2 are needed (wording your call). B1–B3 (blank lines)
   are optional.
3. **Commit form.**
   - (a) **Recommended:** `git am -3` the six patches as delivered (workflow.md §4: authorship kept),
     then the maintainer's edit commit. Each commit elaborates, so the series is bisectable.
   - (b) The same with the subjects' "(F3 cont2, checkpoint N)" dropped.
   - (c) One squashed commit with a public-facing subject, e.g. "WindowClock: the
     configuration-count runner, proved by Route A over field cells".
4. **F6: the order against #156.**
   - (a) **Recommended: land #156 first** (`lphl2` passed; gate 69 round 2 pending), then this PR
     on the campaign branch with its 2-module replay from a copy of `oleans-lphl2` (on which the
     delivered file already elaborates cleanly, row 22).
   - (b) Land this first: replay the 2 modules from a copy of `oleans-lslsk` (exact for the tip's
     Lean). Then #156, after merging the campaign branch, replays the merged tree: its tree differs
     from `lphl2`'s only in WindowClock, so the 2 modules from a copy of `oleans-lphl2` suffice.
   In both cases: never compose snapshots, and never append the root `TCSlib` to a replay list.

## Landing

**Not yet clear to merge**: the landing PR is not opened, replayed or gated, and decisions 1, 3 and
4 are pending. It becomes clear once they are ruled, the PR's base is the campaign branch, its
replay has passed and its fill gate is recorded.

**Land (full): yes**, by a maintainer PR into `complexity/arora-barak-ch3-4`.

**Commits** (from the verified bundle, prerequisite `968d7b2bfbcd9635d8a763673731c89f1a125eda`; or
`git am -3` of the six patches; they apply cleanly at `6e8db28f` and on #156's `0e5f210b`, and the
current tip `aad8a095` has the same Lean tree as `6e8db28f`):
1. `475ecdd0bf118a9eed92d2051ff18b31d21f6cbf` — the writer's host and one field's round;
2. `4619561316f94dd9c62c8179ef369549a7e33957` — one pass;
3. `0ea338d0671254867ef8132c4235302efbe64e1b` — the `c` passes with the record's rewind;
4. `a468d65d9c7c19a050472a5b2a94be5829369b70` — the clock head's rewind;
5. `aaf09900e3016a6b88d0846be79019972ea41cb8` — the writer's contract;
6. `ebca0bc53382464f7ff674909e8ac3aa5fb673e6` — the target proved.

Then **the maintainer's edit commit**: A1, A2 (and optionally B1–B3) from `scripts/landedits.py`
(diff in out/39; checked in out/40). Re-run the v3 screen on the edited file before the gate
(expected: unchanged; only comments and blank lines move).

**Replay** (link `.lake/packages` in the PR worktree; precheck that the Lean diff from the snapshot's
tree to the PR head is exactly `SpaceComplexity/WindowClock.lean`):
- list: `TCSlib/Complexity/SpaceComplexity/WindowClock`, then `TCSlib/Complexity/SpaceComplexity`
  (out/35); not the root `TCSlib`;
- from a copy of `oleans-lslsk` if this lands before #156, or of `oleans-lphl2` if #156 lands first
  (decision 4);
- expected: 0 failures; WindowClock no diagnostic; the facade 0; the order list 28 → 27.

**Review table for the PR body:**
- integrity: 82/82 sums; bundle (sole prerequisite the base); 6 linear commits, owned file only;
  patches = bundle = file (blob `71327d9d`);
- scope: regions (a)–(c) only; imports unchanged; 4 → 4 public declarations, no statement changed;
  55 new `cw_` privates, 2 restated; new public constants only the target's auxiliaries and
  `cw_Idx`'s derived instances (no clash);
- elaboration: no diagnostic at the base and on both of #156's trees; checkpoints bisectable;
- axioms: the target and all 70 within `[propext, Classical.choice, Quot.sound]`, no `sorryAx`;
- rule 10: 34-definition seal, 34/34 controls; no definition passed to `rw`/`simp`/`unfold`;
  rule 11 clean;
- probes: import (102 and 145), consumer, join: as expected;
- lint 0 FAIL, 81 → 82 WARN (size);
- v3 screen: 1,058 → 1,102 declarations, 513 → 521 pairs; 8 new in-file (≤ 88%), 0 cross-file;
- sweep 28 → 27.
