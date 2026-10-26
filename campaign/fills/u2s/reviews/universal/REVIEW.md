# Review — U2, the `k`-tape universal machine: U2-U `Turing.exists_selfUniversalK` and U2-E `Turing.universalK` (`TuringMachine/UniversalK.lean`), megafill C item 1, delivery `fill-u2s-universal.zip`

Read-only review by the maintainer's review sub-agent, 2026-10-26 (UTC). Every claim cites a saved
output under this folder (`out/NN-*`). The zip, its REPORT.md, logs, probes, Lean files and
scripts are data. Nothing from the zip was run. The worker's probes and seal files were copied
into my worktree and elaborated there; I scanned them first: they hold only `#check`/`#print`
lines, or the module with an attribute block. Lean ran only through `tools/leanelab.sh`
(`scripts/elab.sh`), one elaboration at a time. There was no build or cache command. The v3
screen ran once, niced, under `locks/screen.lock` (`scripts/screen.sh`). Python that read the
zip ran with `python3 -I`, from `scripts/`.

**Verdict: complete (2/2) with no admission. Land, by a maintainer PR plus a fill gate, with
three tested dedup edits (F1, D1–D3) and the status edits (F3/F4, S1–S6). Not yet clear to
merge:** there is no PR, replay or gate yet, and the landing order against #164/#167 is the
user's call (decision 4).
- The delivered file elaborates with **0 errors and no diagnostic**:
  - at the base, against `oleans-lkit2` (out/04);
  - at the current tip `6da114a5`, against `oleans-lg4c4m`, with the series and the landing
    edits applied (out/49). #165 merged during this review, and the tip's Lean tree is
    exactly #165's head.
- Both targets and `Turing.exists_selfUniversal` (SelfUniversal, inlined after the new module)
  depend on `[propext, Classical.choice, Quot.sound]`. Their sorry-source walks are empty, and
  all 81 prints are within the standard three (out/05b). At the base the same three consumers
  carried `sorryAx` (out/05d).
- The constants are as REPORT says, chosen before the input:
  - U2-U: `C = T + 1 + D + B + N(2D + 1) + N`, with `D = 50(|tableBitsK| + 1) + C_L` and
    `N = K + k + 2`.
  - U2-E: `C = T_A + 1 + C_R(ℓ + 1)D = T + 2ℓ + 5 + C_R(ℓ + 1)D`, with no `|x|` term.

What passes:
- **Integrity:**
  - 405/405 sums;
  - the bundle's only prerequisite is the base, and its head is
    `deliver/fill-u2s-universal-in`;
  - 5 linear commits, no merges, touching only the owned file (+1,127/−2);
  - patch-ids equal commit-ids, and `git apply` of the 5 patches gives the head tree, at the
    base and at the tip;
  - the dispatch hashes REPORT quotes are correct.
- **Scope:**
  - 5 hunks, all in regions (a)–(d), and the first commit is exactly the overlay.
  - Byte-identical to the base: the header and status (29–32), the startup section and its
    39 `ss_` privates, and both targets' docstrings and statements.
  - Publics 12 → 12; 28 new `uk_` privates, none removed or changed.
  - No `section`/`open`/`variable`. Widths ≤ 97 characters.
- **Rule 10:**
  - My seal: 27 other-file definitions, plus two `[-simp]` erasures, plus the two
    `RewindPhase` instances. The body has 0 errors, and all 31 controls fail sealed and close
    unsealed.
  - The tactic arguments are 229 occurrences and 160 identifiers, classified in the
    environment. They name no other-file definition and no core/Mathlib definition.
- **Rule 11:** no R3 row, and no other file's private, as text or among the elaborated
  constants.
- **Probes:** the brief's 93 checks and the worker's 593 checks (which cover all 563 direct
  external constants) both give 0 errors.
- **Screen:** 1,057 → 1,085 declarations and 788 → 793 pairs. There are 5 new pairs, all
  in-file, none at 90% or more, and no cross-file pair. My output is byte-identical to the
  worker's final screen.
- **Lint:** 0 FAIL, 67 WARN over 84 files at both the base and the head (the brief's 68/83
  was stale). Every proof over 20 lines has a literal "Proof sketch".
- **Sweeps:** the bootstrap has the base's 26 sorries by name. The final set is 24 by name:
  the base minus the two targets.
- **Environment:** v2.5 is followed: the floors, the archive store logged first, 40 roots
  (equal to my computation), and the manifest.

Findings (none blocks the mathematics):
- **F1 (major, failure mode 5 / ground rule 5; fixed by the tested edits D1–D3).** Three
  inline arguments re-derive lemmas that are published and in the import closure. The text
  screen and the worker's statement-level semantic search both miss them. `exact?` closes
  each restated goal with exactly the published lemma (out/27).
  - (a) `uk_loop_forward` (head 1881–1890) re-proves `MultiTapeTM.exists_first_halt`,
    line for line.
  - (b) `exists_selfUniversalK` (2128–2132) re-proves `MultiTapeTM.visitedByTapeHead_mono`.
    The brief named this lemma.
  - (c) `exists_selfUniversalK`'s `hfreeze` (2145–2161) re-proves
    `FinTM.ComputesInTime.spaceUsed_le_of_halt`.
- **F2 (route refinement; decision, accept recommended).** The ruler is tape `k + 2`, not the
  last tape. The brief's σ conditions still hold. No row is affected.
- **F3 (minor, docs).** REPORT's proposed U2-E `**Implementation.**` paragraph is accurate but
  thin, and it points to private lemmas. A drafted replacement is tested (S3).
- **F4 (minor, landing edits).** Stale status text in `UniversalK`, `SelfUniversal` and the
  facade. Drafted and tested (S1, S2, S4–S6).
- **F5 (minor, process).** E-CHK: 3 grouped checkpoint zips for 10 checkpoints, all five of
  phase 2 in one commit. Disclosed, with no effect on the content. The cp zips and the
  cover's `megafill-c-REPORT.md` are not in the inbox.
- **F6–F9 (notes):**
  - F6: the worker's seal leaves out 2 reached definitions and has no `[-simp]` control;
    mine covers both.
  - F7: dedup and promotion items for the maintainer's window, including A+'s in-flight
    `seamCompTM_step`.
  - F8: the last commit cleared a 56% idiom-level cross-file text pair by rephrasing.
  - F9: brief and records accuracy.

## Inputs

| Input | Identity | Evidence |
|---|---|---|
| Zip `exchange/inbox/fill-u2s-universal.zip` | SHA-256 `1834327679968d9276a9de60b17cfea13d70d1d1296893fd25f6dfb4484600f7` (as given); 406 members; no absolute or `..` entry, no symlink | out/01 |
| `SHA256SUMS` | 405/405 OK; covers every member except itself | out/01 (`scripts/sumcheck.py`) |
| Bundle | `verify` okay; one ref `refs/checkpoints/fill-u2s-universal` = `2410022fee818a1206616571e6a972db9338a150` = `deliver/fill-u2s-universal-in`; sole prerequisite `ed8f2e87146be90eb76216e9bc34f7838ec79574` | out/01 |
| Brief `exchange/outbox/fills/u2s-fill-universal.md` | `7213901f…6350` (as given) = base's `campaign/fills/u2s/briefs/u2s-fill-universal.md` with its 4 `@ANCESTOR@` := base; unchanged at the tip | out/01 |
| Cover `megafill-C.md`, addendum v2.5 | `132031ca…7b96` = base copy with 2 `@ANCESTOR@` := base; addendum `90851511…abf0`, unchanged base → tip. The worker's `base-and-attachments.log` records the same three hashes | out/01 |
| Brief inputs | the overlay, import probe, route probe, seal controls, dup probe and screen population: blobs equal at the base and the tip; 97-module order list; base sorries (26 in 11 modules); screen base | out/01, out/36, out/37 |
| Base / tip | base `ed8f2e87` (records only over #162's `5a258cc2`: 0 `.lean` differences). The records worktree was at `46772827`, not the stated `8d46d6bb` (its child, `backlog.md` only). The tip then moved to `98a66d07` and, **during this review, to `6da114a5`: #165 merged** (`f0df8ee5`, 01:42Z). The tip's TCSlib differs from #165's head `308838e5` only in `Build/README.md`. `UniversalK` is blob `4de5324e` at the base and at every tip | out/01, out/43 |
| Snapshots | `oleans-lkit2` (the base's tree); `oleans-lg4c4m` (= #165's head = the current tip's Lean) | out/41, out/43 |

**Review worktrees** (detached under this folder, each with the `.lake/packages` link; left in
place):
- `wt-base` at the base;
- `wt-head` at the head (the screen root; never edited);
- `wt-am` at the base with the 5 patches `git apply`'d;
- `wt-probe` at the head, for probes;
- `wt-land` at the head with the landing edits;
- `wt-tip` at `6da114a5` with the series and the landing edits applied (no commits).

Probes are in `probe/`, scripts in `scripts/`. One slip: I wrote one stray scratch copy to
`/tmp/nonexist` and deleted it at once; nothing else was written outside this folder. I used
one `git stash`/`pop` in `wt-tip`, and `git stash list` is empty afterwards.

## Checks

| # | Check | Result | Evidence |
|---|---|---|---|
| 1 | Zip, sums, bundle, ref | As in Inputs. The intake is reproduced | out/01 |
| 2 | Commits | 5 linear commits, `26e2f43a` … `2410022f`. Author `Codex <codex@openai.com>`. 23:35–00:46Z, inside the item's window. Equal to REPORT's final commit and to its checkpoint table's commits | out/01, out/39 |
| 3 | Patches → head | Each patch-id equals its commit's. Applied at the base (`wt-am`) and at the tip (`wt-tip`), they give blob `0f73b67a`, which is the zip's `UniversalK.lean` (SHA-256 `2641416e…10c7`) | out/01, out/49 (`wt-tip`) |
| 4 | First commit = overlay | `26e2f43a`'s file is byte-equal to `UniversalKOverlay.lean.txt`: one import, `Build.Rewind`, after line 11 | out/01 |
| 5 | Regions | 5 hunks, at base lines 11 (a), 1688 (b, +343), 1725 (d: `  sorry` → 113), 1728 (c, +568) and 1760 (d: `  sorry` → 102). Region (e) is unused. Byte-identical: base 1–1688 (header, status 29–32, scheme, the startup and its 39 `ss_`), U2-U's docstring and statement (base 1689–1724), U2-E's (1729–1759), and the tail | out/02b |
| 6 | Freeze, declfreeze v4 (qualified names) | Public 12 → 12; none added or removed; the two targets are "authorized body change". Private 39 → 67: 28 added, all `Turing.uk_*`; none removed or changed. `privstmt`: no statement changed. `stmtcheck`: every base code line is in the head in order, apart from the two `sorry`s | out/02 |
| 7 | Generated public constants | `Turing.exists_selfUniversalK._proof_1_{1..11}` and `Turing.universalK._proof_1_{1..6}`, compiler auxiliaries. Nothing else new | out/05c |
| 8 | Hygiene (1,127 added lines, code) | no `sorry`, `admit`, `axiom`, `unfold`, `delta`, `set_option`, `open`, `section`, `variable`, `attribute`, `instance`, `deriving`, `native_decide`, `simp_all`, `aesop` or `norm_num`. No unrestricted `simp`/`simpa`. Two `noncomputable def`s (`uk_loopTM`, `uk_suffixStartupTM`). Six `decide`s, on core `Fin`/`Bool` facts | out/03 |
| 9 | Widths and size | Added lines are at most 97 characters, the whole file at most 98. 1,762 → 2,887 lines; 12 public / 67 private (lint INFO). Size is not a driver | out/03, out/30 |
| 10 | Elaboration, head at base (`lkit2`) | exit 0, **no diagnostic**. The base file gives exactly 1716/1754 `declaration uses 'sorry'` | out/04 |
| 11 | Elaboration at the tip (`lg4c4m`) | `ZoneRebalance` and the facade are not upstream of `UniversalK`, so the delivered file needs no merged run. I ran one anyway, because #165 merged: the series plus the landing edits at `6da114a5`. `UniversalK` and the facade: exit 0, no diagnostic | out/41, out/49 |
| 12 | Axioms, 81 prints (all 79 declarations of the module + `exists_selfStartupTM`, `exists_selfUniversal`, with SelfUniversal's body inlined after the new module) | all within `[propext, Classical.choice, Quot.sound]`. Direct `sorryAx` users in the closures of the targets, the startup and both SelfUniversal theorems: `[]` | out/05, out/05b |
| 13 | Consumers made admission-free | `Turing.exists_selfUniversal` had `sorryAx` at the base (via `exists_selfUniversalK`) and is standard after this landing. `SpaceComplexity/Hierarchy` does not import SelfUniversal: its `U₀` results stay sorried statements. `Turing.universal`'s re-derivation from U2-E (the deferred retrofit) is now unblocked | out/05d, out/44 |
| 14 | The brief's import probe (93 checks) | 0 errors, 0 warnings. Its five axiom prints are the standard three | out/07 |
| 15 | The worker's `FinalImportProbe` (593 checks, 593 distinct names) | 0 errors. Two deprecation warnings (`Int.ofNat_mul`, `Int.ofNat_nonneg`): core names that appear among the elaborated constants (out/05) but not in the source, presumably from `omega`'s terms. It covers **all 563** direct external constants of my walk, including the startup boundary (out/07b) | out/07, out/07b |
| 16 | Rule 10, seal (27 definitions: `Cfg.init`, `Cfg.inputSymbol`, `Cfg.mapState`, `Cfg.workTapeSymbols`, `FinTM.ComputesFunInTime`, `FinTM.ComputesInTime`, `FinTM.bufferTape`, `MultiTapeTM.initCfg`/`runFrom`/`spaceUsed`/`spaceUsedByTape`/`step`/`visitedByTapeHead`, `StepBlock.forwardLoopCfg`/`summaryCells`, `tableBitsK`, `embedEmitCfg`, `embedEmitTM`, `inputMoveAction`, `tapeAction`, `moveInputPos`, `pairEncode`, `unaryFin`, `rewindTM`, `rulerHostCfg`, `seamCompTM`, `serializeK`; `[-simp]` on `Cfg.init` and `MultiTapeTM.initCfg`; extended with `instDecidableEqRewindPhase` and `instFintypeRewindPhase`) | Placed at the top of region (b), so it covers everything new. Sealed: **0 errors in the body**, and 29 (31 extended) errors, one per control. Unsealed: 0 errors. The list is every reached other-file definition that is not a projection, instance or constructor (my walk; the statements of the cited lemmas reach no further definition) | out/21-*, out/05 (DIRECT-TCSLIB) |
| 17 | The worker's seal and controls | `UniversalKFinalSealed` (25 definitions): 0 errors. Its 25 controls: 25 errors sealed, 0 unsealed. It leaves out `FinTM.ComputesFunInTime` and `serializeK`, which are reached only through `EffectiveCodeK`'s structure, and has no control for the two erasures (F6) | out/22-* |
| 18 | Tactic arguments | 229 occurrences, the same count as the worker's `final-inspection.md`. Of 160 identifiers: 111 theorems; 8 definitions, all owned (`EffectiveCodeK.toFinTM` and six `uk_` definitions in `dsimp`/`simp`/`rw` lists), plus the core simproc `↓reduceIte`; 41 locals. **No other-file TCSlib definition and no core/Mathlib definition is passed to `rw`/`simp`/`dsimp`/`unfold`**. There is no `unfold` | out/20, out/20b |
| 19 | `show`/`change`/`rfl` | `change` and `show` expose owned definitions (`uk_scanCfg`, `uk_suffixCfg`) or arithmetic. The 47 `rfl`s close owned-definition projections, structure literals, core `List.drop`/`Option.map`/`Fin` facts and Mathlib's `Fin.castLEEmb` (allowed by the 2026-10-23 scope). All pass under the seal (row 16). The unsealed `rfl` that closes `uk_loop_init` (REPORT) is not used: the proof cites `uk_init_mapState`, with `rfl` only for `uk_loopTM`'s own `q₀` field | out/20, out/21, head 1830 |
| 20 | Equation lemmas in the terms | No `X.eq_N`, `X.eq_def` or `_unfold` of any other-file definition. Present: `List.IsPrefix.eq_of_length_le` (a theorem), auxiliary `_proof_N`s from published statements, the core `eq_true`/`eq_false`/`eq_self`, and the owned `uk_loopTM.eq_1`, `uk_headerTM.eq_1`, `uk_suffixStartupTM.eq_1` | out/05 |
| 21 | Rule 11 | No R3 row, as text or among the elaborated constants. No other file's private among the elaborated constants. Text hits against 5,610 other-file privates are spelling collisions only: `S`, `T`, `one`, `trans`, and `mapState_state`, which is the public `Turing.Cfg.mapState_state` in the walk. `uk_` is unused elsewhere at the tip and on every branch | out/23, out/05, out/43 |
| 22 | v3 screen (script `f4feac91…f181`), at the head, 20 files, 412 s, 3.47 GB | `1,085 declarations; 793 pairs; 214,252 chars`. **Byte-identical to the worker's `screen-final-repair.txt`** (REPORT's final). The worker's before screen is byte-identical to the screen base | out/24, out/25 |
| 23 | New pairs (`pairdiff.py`) | **5 new, 0 gone, 0 cross-file**, all `UniversalK` in-file, 57–61%, equal to REPORT's five. The one cross-file pair touching the file is the base's `ss_inputRewind_run`/`timedFrame_run` (56%) | out/25 |
| 24 | Semantic duplication | 3 re-derivations (F1). The other 28 statements are not published (table below) | out/26–29 |
| 25 | Proof sketches and docstrings | All 28 new declarations have a docstring. Every new proof over 20 lines has a literal "Proof sketch" (`uk_encode_init_tapes` 30, `uk_embed_init` 29, `uk_loop_space` 64, `uk_scan_step` 32, `uk_scan_pair` 52, `uk_scan_header` 48, `uk_header_run` 63, `uk_suffixStartup_run` 117, `uk_embed_suffix` 53; the targets keep their frozen sketches) | out/31 |
| 26 | Public-facing text | The 28 new docstrings (out/35) have no campaign label, path, date or session word ("U2", "H2-F", "H5", "R1"/"R2", "checkpoint", "gate", "brief", …: no hit). The leaf's docstring says "No public row writes a ruler of the doubled header's length", as the brief asks | out/35 |
| 27 | Lint | base `0 FAIL, 67 WARN over 84 files`; head the same. `UniversalK`'s WARNs are its size and the two pre-existing public definitions. **The worker's 67/84 is right; the brief's 68/83 was stale** | out/30 |
| 28 | Bootstrap (overlay) | 97/97 in list order, exit 0, no error. **26 sorry warnings = the base set by name**; `UniversalK` at overlay lines 1717/1755 | out/36 |
| 29 | Final sweep + tail | The sweep (97 modules at `dbc08423`) and the tail rebuild after commit 5 (`UniversalK` and the six later modules, 00:46:49–00:49:07Z, at `2410022f`) both exit 0 with no error. **24 sorry warnings = the base minus the two targets, by name** (modules 1–90 from the sweep, 91–97 from the tail). The tail covers every module after `UniversalK` in the order list, and so the whole downstream closure (`SelfUniversal`, the facade). `lean_check_tree.sh` writes oleans, so the tail is sound (the other four tail modules are not downstream; checking them is harmless) | out/36, out/37 |
| 30 | Environment (v2.5) | Preflight: 9 CPUs; free 28.90 GiB (floor 12); headroom `8,589,934,592 − (99,332,096 + 106,938,368 + 0) = 8,383,664,128` bytes = 7.81 GiB (floor 4); oom 0. Before the item: 25.2 GB free. The archive store was **logged first: absent, 0 files**. Narrowed fetch: 1,002/1,002 downloaded and unpacked; **40 roots = my computation** from the 97-module list; the list is import-closed and in order. Manifest PASS (11 present, 4 doc packages absent); 0 empty oleans. Part 2: the condition occurred; the shim's source (SHA-256 `985924ad…4fba7`) is **byte-equal to the addendum's only C block** (not compiled here). Memory logged per module (97/97/12) with `os.wait4`. No `lake build`. The fetch's command line is not in `cache-get.log` (F9) | out/38, out/37 |

**The construction** (head 1690–2885; all bodies read):
- **U2-U.** `U := uk_loopTM R exit L entry`, that is,
  `{ seamCompTM R exit (embedEmitTM (Fin.castLEEmb _) L) entry with q₀ := Sum.inl R.q₀ }`.
  - `R`, `exit`, `T`, `B` come from `exists_selfStartupTMK k E`; `L`, `entry`, `C_L`, `cost`
    from `exists_forwardLoopTM k`.
  - The seam's initial configuration is read through `runFrom_with_q₀` and the general
    transport `uk_init_mapState`, which is proved from the published `initCfg_eq` and the
    `Cfg.init_*`/`Cfg.mapState_*` equations.
  - `uk_embed_init` identifies R's endpoint (the startup's statement) with the R1 embedding of
    `forwardLoopCfg entry M (M.initCfg z)`, through `embedEmitCfg_eq` and
    `uk_encode_init_*`.
  - Time: the first halt `t₀`, then `Lockstep.runFrom` and the per-step bound.
  - Space: `uk_loop_space`, by `seamCompTM_visitedByTapeHead_ofCfg`,
    `embedEmitTM_visitedByTapeHead`/`_frame`, `spaceUsed_eq_sum` and
    `spaceUsedByTape_eq_card`, with H2-F's ledger for the mirrored tapes (⊆ M's visited sets)
    and the auxiliary tapes (⊆ `Icc (−D) D`).
  - Converse: `uk_loop_pre_live` (the prefix is live), `uk_loop_run`, then `uk_loop_converse`:
    `uk_loop_live` (positive costs and `Lockstep.cut`) and `runFrom_output_eq_of_halt`.
- **U2-E.** `U := uk_loopTM (k := k + 1) A finish H (inj entry false)`, where:
  - `A = uk_suffixStartupTM R exit` is R embedded by R1 in `K + (k + 3)` tapes, seamed into
    `uk_headerTM ⟨k + 2, _⟩` (the leaf `uk_scanTM`, seamed into the public `rewindTM`);
  - `H`, `inj`, `C_R` come from `exists_rulerHostTM L`.
  - `uk_suffixStartup_run` reaches `uk_suffixCfg` at exactly `T + 1 + (2ℓ + 3)`, with its
    first-return cut. `uk_embed_suffix` identifies it with the R1 embedding of
    `rulerHostCfg ℓ hz (c.state.map fun q => inj q false) c (bufferTape (replicate ℓ true)) 0`.
  - H5 is used as stated: `hz`, `0 < ℓ`, `pairEncode_drop α x` (cited, no copy), the ruler
    hypothesis at `rp = 0`, and the tag `false`, since `c.inputPos.val = 1`.
  - Forward: `host v` at `L`'s encoded halt time `v`.
  - Converse: `host (v + 1)`'s cut shows `L` halts; `host r`'s endpoint and two
    `runFrom_output_eq_of_halt` give the output.
- **C60-1.** Only `exists_rulerHostTM` is consumed (no `exists_rulerDeviceTM`). The host's
  configuration is cited at the times H5 states. After them only its **halt** is used, never a
  device exit. `inj` is used only as a function, and no injectivity is assumed or available.
- **Edge cases.** The proofs carry no hypothesis beyond the frozen statements. So `k = 0`,
  `w = []`/`x = []`, `α = []` (`ℓ = 2 > 0`), a canonizer with no work tapes (inside the
  startup's `K`), any `E.canonizerTime` (`T`, `B` per code) and a nonhalting coded machine
  (`uk_loop_live`) are all instances of what the kernel checked. The converses are proved
  arguments, and the forward clauses make them non-vacuous.

| Item (brief route) | Status | Notes |
|---|---|---|
| 1.1 Seam into H2-F, explicit `q₀` | **as briefed** | `seamCompTM` + R1 (`embedEmitTM`, not R1′) on the first `k + 2` tapes; `runFrom_with_q₀`. `initCfg_with_q₀` is used in `uk_suffixStartup_run`; for the loop's initial configuration, `uk_init_mapState` does the work that `initCfg_with_q₀` would leave anyway |
| 1.2 Forward ledger | **as briefed, F1(a)** | the first halt by hand rather than `exists_first_halt` (the brief allowed "or the least such time"), but its absorption step is that lemma's third clause, copied |
| 1.3 Space ledger | **as briefed, F1(b)(c)** | `visitedByTapeHead_mono` (named by the brief) and `ComputesInTime.spaceUsed_le_of_halt` re-derived inline; `spaceUsedByTape_le_card_Icc` is not needed (the subset is direct) |
| 1.4 Converse (input-generic `uk_` lemmas) | **as briefed** | `uk_loop_forward`/`_live`/`_converse` are generic in `x`; phase 2 cites them |
| 2.1 Header ruler (the authorized leaf) | **as briefed** | one leaf (`uk_scanTM`, 4 states); its run for any offset `1 + p` with `z.drop p = pairEncode u v`, overwriting `2|u| + 2` cells from any ruler head (two-header ready); cells read through `inputSymbolInner`, `List.getElem_drop`, `pairEncode_eq`; steps by `step_of_tapeAction_write`, `moveInputPos_pos_of_ne_right`; rewind by `rewindTM_run_ofCfg` at `n = ℓ` |
| 2.1 Tape layout | **refined (F2)** | ruler on tape `k + 2`; host along `Fin.castLEEmb` (k + 3 ≤ K + (k + 3)) |
| 2.2 Host start | **as briefed** | tag `false`; `uk_ruler_fields` via `rulerHostCfg_*` |
| 2.3 Forward ledger, no `|x|` | **as briefed** | `C` before `x` |
| 2.4 Converse | **as briefed** | H5 cut with `t ≤ t'`, then phase 1's converse |
| Joins | **as briefed** | R2 `seamCompTM` throughout; no phase host, second loop, input device, input rewind or layout machine |

## Findings

| # | Severity | File · declaration | Claim | Evidence | Proposed resolution |
|---|---|---|---|---|---|
| F1 | **major** (failure mode 5; ground rule 5 "Cite proved material; never re-prove it") | `UniversalK` · `uk_loop_forward` (head 1881–1890); `exists_selfUniversalK` (2128–2132; `hfreeze`, 2145–2161) | Three inline arguments re-derive published lemmas, all in `UniversalK`'s import closure (`Finite`, `SpaceComplexity/ConfigCount`): (a) `Turing.MultiTapeTM.exists_first_halt`, the same proof text (`Nat.find`, `find_min'`, `find_min`, `runFrom_add` + `runFrom_of_halt`); (b) `Turing.MultiTapeTM.visitedByTapeHead_mono` (named by the brief, route step 3); (c) `Turing.FinTM.ComputesInTime.spaceUsed_le_of_halt`. The text screen misses them (renamed variables), and REPORT's semantic search screened only the statements of new privates, not the inline arguments | out/27-dup-exact-summary.txt: `exact?` closes the three restated goals with `MultiTapeTM.exists_first_halt M (MultiTapeTM.initCfg x) hhalt`, `MultiTapeTM.visitedByTapeHead_mono M (MultiTapeTM.initCfg x) ht₀ j` and `FinTM.ComputesInTime.spaceUsed_le_of_halt h hs t₂`; out/29 | **Apply D1–D3 in the landing PR** (`scripts/dedup_edits.py`; out/28-dedup-edits.diff, −28 lines). D1 is `obtain ⟨t₀, hle, hfirst, hsame⟩ := MultiTapeTM.exists_first_halt M (M.initCfg x) hhalt`. D2 is `Finset.card_le_card (MultiTapeTM.visitedByTapeHead_mono M (M.initCfg z) ht₀ j)`. D3 is `hUcomp := (computesInTime_iff …).mpr ⟨hUhalt, hUout⟩`, then `FinTM.ComputesInTime.spaceUsed_le_of_halt hUcomp hspace _`. Tested: no diagnostic (out/28), the 31-control seal (out/28-dedup-edits-sealed), axioms unchanged (out/46-land-axioms-compare.txt). No new import. Lesson for briefs: never offer "or re-derive it" next to a named lemma |
| F2 | note; **decision (accept recommended)** | `UniversalK` · `uk_suffixStartupTM`, `uk_suffixCfg`, `universalK` | The brief said "U2-E's machine has one more tape … the ruler, last". The delivery places the ruler on tape `k + 2`, right after the simulation bank. `R` keeps tapes `0 … K + k + 1` and the new tape is `K + k + 2`. When `K ≥ 1`, the ruler reuses R's first auxiliary tape, which R's endpoint leaves blank with its head at 0 (the startup's statement), and the last tape stays idle. When `K = 0` they coincide. The brief's own σ conditions (`σ j.castSucc = ⟨j, _⟩`, `σ (Fin.last _)` = the ruler) hold for `σ = Fin.castLEEmb`, and every named row is used as named. REPORT states the layout but does not flag it as a departure | head 2523–2539, 2570, 2703; REPORT §Construction | Accept. "Binding where it names a row": no row is involved. U2-E has no space clause, so the idle tape costs nothing, and the layout is invisible through the statement (`∃ U`). The ruler-last variant would need a custom embedding for no gain |
| F3 | minor (docs) | `UniversalK` · `universalK`'s docstring | REPORT's proposed `**Implementation.**` paragraph is accurate and has no campaign label. But it names no row (`exists_selfStartupTMK`, `rewindTM`, `rulerHostCfg`, `exists_rulerHostTM`, `exists_forwardLoopTM`), gives neither the tape placement nor the constant, and points readers to private lemmas ("Reuse the self-universal proof's loop run, divergence, and seam lemmas") | REPORT lines 106–114 | Use S3 (out/45-landing-edits.diff): the steps in order, the tapes (`K + (k + 3)`, ruler on `k + 2`), `T + 2ℓ + 4` steps to the host's start with the tag `false`, and `C = T + 2ℓ + 5 + C_R (ℓ + 1) D`. Tested (out/46–49) |
| F4 | minor (landing edits) | `UniversalK` header (29–32), Main results (63–66), U2-E docstring (2763–2765); facade `TuringMachine.lean` (255, 258); `SelfUniversal` status (24–29) | All still call the two contracts sorried, the U2 statement gate pending, or the retrofit "deferred until this statement is filled" | out/44 | S1, S2, S4, S5, S6a/b, drafted and tested. Rewritten sentences drop the campaign labels ("H2-F", "U2-U"/"U2-E", "U-1"), the `audits/` path and the dated rulings. Leave the stale "(the fill gate, with U2-S and U2-U, is pending)" in `Build/StepBlockForward.lean` line 16 for the deferred docstring cleanup: that file is upstream, and editing it would widen the replay to its whole downstream closure |
| F5 | minor (process) | delivery | E-CHK, disclosed: 3 grouped checkpoint zips for 10 checkpoints. cp1 at `64d629fb` holds 1.1 and the loop parts of 1.2/1.4; cp2 at `59c24034` holds U2-U; cp3 is the final. All of phase 2 (2.1–2.5) is one commit, `dbc08423` (+720/−67), so a session ending mid-phase-2 would have lost all of it. No effect on the delivered content. The cp zips (REPORT gives their SHA-256s and says they were "delivered immediately") are not in the inbox, and neither is the cover's session report `megafill-c-REPORT.md` (Delivery, Part 3 item 6) | out/39 | Accept, with no re-delivery (decision 5). Confirm whether the cp zips and the session report arrived elsewhere. For the next cover: ask for a commit per numbered checkpoint even when the zips are grouped |
| F6 | note (rule-10 records) | `evidence/UniversalKFinalSealed.lean`, `ControlsRuler*` | The worker's 25-definition seal leaves out `FinTM.ComputesFunInTime` and `serializeK` (reached only through `EffectiveCodeK`'s fields) and has no control for its two `[-simp]` erasures. It is still sound | out/22, out/21 | None. My 27-definition seal plus 2 erasures plus 2 instances, with 31 controls, passes (row 16) |
| F7 | note (dedup window / promotion) | `UniversalK` | (i) `uk_init_mapState` is the general form of the startup's inline `hinit` (head 1583–1598); the same fact is an ad hoc `rfl` in `NDHost` and `Relativization`. Promotion candidate: a public `MultiTapeTM` lemma beside `initCfg_with_q₀`. (ii) `uk_loop_forward`/`_live`/`_converse` are generic consequences of `exists_forwardLoopTM`, and `Complexity.space_universal` will need them; promotion candidate, a public corollary beside H2-F. (iii) A+'s in-flight `Turing.seamCompTM_step` packages the `seamCompTM_run_ofCfg` + `_firstReturn_ofCfg` pair that `uk_header_run` and `uk_suffixStartup_run` compose inline; re-point after A+ lands. (iv) REPORT's two promotion candidates (the seam into H2-F, the header-ruler scan) are agreed | out/29, out/26 | The maintainer's window, not this landing |
| F8 | note (screen) | `uk_scan_pair` (commit 5) | Before commit 5, `uk_scan_pair` reproduced 56% of `Universal`'s private `timedFrame_run`, a cross-file pair. Commit 5 rephrased the two-step unrolling (`runFrom_add` with a local one-step `have`). Both texts are the generic step-unrolling idiom; neither re-derives the other | out/25 (worker's pre-repair screen vs head) | Accept. The repair is legitimate (no copy before or after) |
| F9 | note (records, brief) | brief, REPORT, logs | The brief's out-of-scope list names `NDCodeSimulator`'s `exists_replayCanonizer`, which is not in the base sorry set (26 entries, none in `NDCodeSimulator`). Its lint base 68/83 was stale (67/84). `cache-get.log` does not record the fetch's command line; the count of 1,002 archives matches a 40-root fetch. The worker's probe has 2 deprecation warnings from names reached only through `omega`'s terms | out/36, out/30, out/38, out/07 | None for the landing; corrections for later briefs |

## Decisions for the user

1. **F1, the three re-derivations.**
   - (a) Apply D1–D3 in the landing PR. **Recommended**: tested, −28 lines, nothing changes
     outside the owned file.
   - (b) Land as delivered and record the three as debt for the 12.2c window.
2. **F2, the ruler on tape `k + 2` instead of last.** Accept: **recommended**. It is
   mathematically neutral and uses only the brief's rows; the alternative needs a bespoke
   embedding.
3. **The status and Implementation wording** (S1–S6, out/45-landing-edits.diff).
   - S1–S3 and S5 are needed: they state the proved status and add the Implementation
     paragraph.
   - S4 (U2-E's "deferred until this statement is filled") and S6a/b (`SelfUniversal`'s stale
     "U2 statement gate pending" and the facade's dated gate line) are optional. All stay
     inside the 3-module replay closure.
   - Recommended: all of them.
4. **Landing order** against the in-flight PRs; details under Landing. Recommended: land
   after #164 (and after #167 if it is ready first), so that their prepared merged-tree
   replays stay valid, and chain U2's 3-module replay from the snapshot they leave.
   - #164's 193-module replay was written at the current tip, and its precheck passed (tip
     commit `6da114a5`).
   - Landing U2 first is sound, but it changes 3 modules in #164's and #167's lists. Both
     replays must then re-run at the merged tree, and #164's precheck ("tip = #165's head")
     must be updated.
5. **F5 (E-CHK).** Accept as a disclosed process deviation, with no re-delivery:
   **recommended**.

## Semantic duplication

Method:
- a statement index of all 7,693 public theorems at the tip, plus every changed file on #164,
  #165, #166, #167, A+ and #135;
- name and pattern greps;
- `exact?`/`apply?` on the module with only the new definitions available. These were 10
  sampled statements to `exact?`, 2 to `apply?`, and 3 control goals restating inline
  arguments (out/26–29).

| New private / inline argument | Published candidates checked | Result |
|---|---|---|
| `uk_encode_init_tapes`, `uk_encode_init_fields`, `uk_encode_halt` | `forwardLoopCfg_*`, `summaryCells_eq`, `initCfg_eq`, `Cfg.init_*` (cited) | not published (the pre-ship dup probe; `exact?` fails on the latter two); authorized route-probe copies |
| `uk_embed_init` | `embedEmitCfg_eq` (cited), `embedEmitCfg_mapState_eq` | layout-specific; not published |
| `uk_loopTM`, `uk_headerTM`, `uk_suffixStartupTM` (defs) | `seamCompTM`, `embedEmitTM`, `rewindTM`, `Fin.castLEEmb` | compositions of public combinators |
| `uk_init_mapState` | `initCfg_with_q₀`, `initCfg_eq`, `Cfg.init_*`/`Cfg.mapState_*`, `MultiTapeTM.relabelState_runFrom_init` (equivalences only), A+'s `embedSilentCfg_initCfg` (in flight; silent embedding) | `exact?` and `apply?` fail; not published; promotion candidate (F7) |
| `uk_loop_init` | instance of `uk_init_mapState` | `exact?` offers only `rfl` (rule 10: rejected; not used) |
| `uk_loop_pre_live`, `uk_loop_run` | `seamCompTM_runFrom_left`/`_right`, `runFrom_state_ne_none_of_le`, `embedEmitTM_runFrom` (cited) | `exact?` fails (`_pre_live`); specific to `uk_loopTM` |
| `uk_loop_forward` (statement) | `Lockstep.runFrom` (cited) | `exact?` fails |
| `uk_loop_forward` (proof, 1881–1890) | `MultiTapeTM.exists_first_halt` | **re-derived (F1a)** |
| `uk_loop_live` | `Lockstep.cut` (cited), `not_halts_of_repeat_nonhalt`, `Contract.live` | `exact?`/`apply?` fail; not published |
| `uk_loop_converse` | `runFrom_output_eq_of_halt` (cited); `FinTM.ComputesInTime.output_unique` (initial configurations only) | `exact?` fails |
| `uk_loop_space` | `spaceUsed_eq_sum`, `spaceUsedByTape_eq_card`, `seamCompTM_visitedByTapeHead_ofCfg`, `embedEmitTM_visitedByTapeHead`/`_frame` (cited); `seamCompTM_spaceUsed(ByTape)_le_add`/`_le_max` (`Cfg.ofWords` seams only); `Contract.spaceUsedByTape_le`; `spaceUsedByTape_le_card_Icc` (head-position form) | not published |
| `exists_selfUniversalK`, 2128–2132 | `MultiTapeTM.visitedByTapeHead_mono` | **re-derived (F1b)** |
| `exists_selfUniversalK`, `hfreeze` | `FinTM.ComputesInTime.spaceUsed_le_of_halt` | **re-derived (F1c)** |
| `uk_scanTM`, `uk_scanCfg`, `uk_scan_zero`, `_step`, `_pair`, `_header`, `_run` | catalog `tapeAction`/`inputMoveAction`, `step_of_tapeAction_write`, `moveInputPos_pos_of_ne_right`, `inputSymbolInner`, `List.getElem_drop`, `pairEncode_eq`, `output_prefix` (cited); `UniversalStartup`'s private `universal_pair_get`/`_separator`, `universalPrefix_bits` (text hazard) | the authorized leaf and its run; no text pair with `UniversalStartup` |
| `uk_scan_ruler` | `FinTM.bufferTape_eq` (cited), `List.getElem?_replicate`; `FinTM.bufferTape_unary` (another statement) | `exact?` fails |
| `uk_header_run`, `uk_suffixStartup_run` | `rewindTM_run_ofCfg`, the seam pair, `embedEmitCfg_eq`, `initCfg_with_q₀`, `Cfg.mapState_mapState` (cited); A+'s `seamCompTM_step` (in flight) | not published at the base; F7(iii) |
| `uk_suffixCfg` (def) | — | owned presentation |
| `uk_ruler_fields` | `rulerHostCfg_*` (cited) | `exact?` fails; authorized route-probe copy |
| `uk_embed_suffix` | `embedEmitCfg_eq`, `rulerHostCfg_*`, `Fin.lastCases_*` (cited) | layout-specific |

The open branches (#164, #165, #166, #167, #135) state none of these statements or a
generalization of one. A+ is noted above (in flight, so not citable).

## Landing

**Recommendation: land (full) by a maintainer PR into `complexity/arora-barak-ch3-4`, plus a
fill gate.** This is the U2 fill's landing, as gate 63 was the startup's.

**Not yet clear to merge.** It becomes clear when all of these hold:
- the PR is open and based on the campaign branch, not stacked;
- the decisions above are taken;
- the replay below has passed;
- the fill gate is recorded with zero blockers and zero majors (F1 closed by D1–D3).

**Commits.**
- Cherry-pick the 5 commits `26e2f43a`…`2410022f` from `deliver/fill-u2s-universal-in`
  (= the bundle's `refs/checkpoints/fill-u2s-universal`; prerequisite `ed8f2e87`, a
  records-only ancestor of the tip), or squash them.
- They touch only `UniversalK`, which is unchanged at the tip (blob `4de5324e`). They apply
  cleanly at `6da114a5` (`wt-tip`, out/49).
- Their subjects begin "U2:": reword if the PR wants library-only wording.
- Add one maintainer commit with out/45-landing-edits.diff:
  - D1–D3 (F1);
  - S1–S6 (F3/F4) in `UniversalK.lean`, `SelfUniversal.lean` and `TuringMachine.lean`.
- The landing edits are tested at the head (`wt-land`) and at the tip (`wt-tip`):
  - elaboration: `UniversalK` and the facade have no diagnostic, against `lkit2` and against
    `lg4c4m`; `SelfUniversal`, inlined after the edited module, has none either (out/46,
    out/49);
  - the axioms are unchanged (out/46-land-axioms-compare.txt);
  - the 31-control seal passes (out/46-land-seal);
  - freeze: no statement changed; `uk_loop_forward` and the two targets change only their
    bodies or docstrings; `SelfUniversal` and the facade are code-identical (out/47);
  - lint `0 FAIL, 67 WARN / 84` (out/48, out/49);
  - widths ≤ 99; no campaign label in the added text; 2,873 lines.
- The facade hunks (255, 258) are disjoint from #165's/#167's (166–167).
- Link `.lake/packages` in the PR worktree.

**Replay.**
- `UniversalK`'s downstream closure is 3 modules, the same at the head and with the edits
  (`mkdownmulti.py`, out/42):
  1. `TCSlib/Complexity/TuringMachine/UniversalK`;
  2. `TCSlib/Complexity/TuringMachine/SelfUniversal`;
  3. `TCSlib/Complexity/TuringMachine` (never the root `TCSlib`).
- Its upstream closure gains exactly `Build/Rewind` (53 → 54 modules, out/41).
- Chain the replay from the snapshot that is exactly the tree the PR merges into:
  - on the current tip, `oleans-lg4c4m` (the tip's Lean = #165's head, out/43);
  - if #164 (or #167) merges first, the snapshot its merged-tree replay leaves;
  - otherwise, the merged-tree closure of every changed file since `lg4c4m`. That is #164's
    193-module list and/or #167's 91-module list; both already end with `UniversalK`,
    `SelfUniversal`, `TuringMachine`.
  - Never compose snapshots.
- Expected: 0 failures, and no diagnostic in all three modules. The 97-module order list
  goes 26 → 24 sorry warnings.

**Order against the in-flight work** (out/43):
- **#165:** merged during this review (`f0df8ee5`). Its facade edit is already the base of
  the landing.
- **#164** (`TimeConstructible`, `SpaceComplexity/Basic`, both upstream of `UniversalK`):
  - Its 193-module replay (from `lg4c4m`, precheck "tip = #165's head" passed) contains
    U2's 3 modules (lines 191–193) and not `Build/Rewind`, so the list stays valid either way.
  - If U2 lands first, #164's replay must re-run at the merged tree, with its precheck
    extended to U2's three files.
  - If #164 lands first, U2 replays its 3 modules chained from #164's snapshot.
  - No merged elaboration of U2 with #164 is possible here: no snapshot of #164's tree
    exists. #164's own replay covers it.
  - None of #164's 10 new public names collides with a token of U2's code (out/43b).
- **#167** (`Build/Contract/Basic`, upstream; now retargeted to the campaign): the same as
  #164, with its 91-module list (lines 89–91).
- **#166** (`Savitch`, stacked on #164): its 2-module list does not touch U2.
- **A+** (`lean/interpreter-startup` `f30210d7`; gate 79; changes `InterpreterStartup` and
  `NDCodeSimulator`, neither upstream of `UniversalK`):
  - Gate 79's screen population includes `UniversalK`, and its screens ran at `a524c36f` and
    `f30210d7`, both before U2. If U2 lands first, gate 79 must re-take its base and head
    screens at the merged tree. Otherwise U2's 5 in-file pairs appear as A+'s, and any A+/U2
    cross pairs are missed.
  - Symmetrically, U2's population includes `NDCodeSimulator`: if A+ lands first, the U2
    fill gate's screen runs at the tree with A+'s `NDCodeSimulator`.
  - Both closures contain the facade, so whichever lands second replays the facade at the
    merged tree.
  - After both land: re-point `uk_header_run`/`uk_suffixStartup_run` at A+'s
    `seamCompTM_step` (F7(iii)).
- **#135** (onto `main`): unrelated.

**What the fill gate's pack should ask** (attach `campaign/standards/TEMPLATE.md`,
`policy.md` and `workflow.md`; the brief, the cover and addendum v2.5; the delivery's REPORT
and evidence; this review with `out/`; and the landing diff):
1. **Correctness against the frozen statements and sketches.**
   - The two constructions and constants above.
   - The converses: U2-U through `uk_loop_live`/`_converse`; U2-E through H5's cut and
     endpoint at `L`'s halt.
   - The edge cases.
   - Is U2-U's frozen sketch accurate as it stands, and is the S3 paragraph accurate for U2-E?
2. **Route conformance.**
   - The seam with the `q₀` override; R1 (not R1′) for `L`, `H` and the startup; the single
     finite-state leaf and its docstring; `pairEncode_drop` cited; the rewind by
     `rewindTM_run_ofCfg`; the tag `false`.
   - C60-1: only the host's statement is used; no device exit; `inj` only a state map.
   - F2: is the ruler on tape `k + 2` acceptable?
3. **Semantic duplication**, at the level of inline arguments, not only private statements.
   F1 and D1–D3; anything else in the 1,127 lines that re-derives a published lemma.
4. **Rule 10.** Is the seal set complete? (27 definitions + 2 erasures + 2 instances,
   31 controls.) Does any `rfl`/`change`/`decide` step close only by unfolding another file's
   definition? Rule 11.
5. **Duplication screen at the landing head:** the edits change text. New pairs against the
   screen base; no cross-file pair.
6. **Public-facing text of S1–S6.**
7. **Process:** E-CHK (F5); the missing cp zips and session report.
8. **The replay** (above) and the order against #164/#167/A+.
9. **Deliverable:** a downloadable `u2-universal-fill-findings.md` with the findings table and
   the verdict line.

**Review table for the PR body:**
- integrity: 405/405 sums, bundle, 5 commits, patches = bundle = file;
- scope: regions (a)–(d), statements and docstrings byte-identical, 28 `uk_` privates, one
  import;
- elaboration at the base and at the tip: no diagnostic;
- axioms: the standard three for both targets and `exists_selfUniversal`;
- rule 10: a 31-control seal; rule 11 clean;
- probes: 93 and 593 checks, 0 errors;
- screen: 1,057 → 1,085 declarations, 788 → 793 pairs, 0 cross-file;
- lint: 0 FAIL, 67 WARN;
- sweep: 26 → 24;
- F1 fixed by D1–D3; status edits S1–S6.
