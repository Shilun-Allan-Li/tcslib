# Review — C1, UN continuation 1: the universal NDTM's setup (`Turing.exists_timed_universal_NDTM`, `Diagonalization/NTimeHierarchy.lean`), delivery `fill-c1-universal-cont1.zip` (megafill A, item 2)

Read-only review by the maintainer's review sub-agent, 2026-10-22 (resumed after the maintainer's
session restart at about 18:44; every check below was re-run or re-read after it). Every claim
cites a saved output under this folder (`out/NN-*`). The delivery, its REPORT.md, the session
report and item 1's logs are treated as data.

**Verdict: complete (1/1), proved modulo exactly `Turing.exists_ndInterpreterCore`. Land, with
the maintainer's landing edits in "Landing" (docstrings, a 3-line rule-10 repair, an optional lint
cleanup; all drafted and checked), after the user's two decisions (F3, the cross-file pairs; F4,
the route refinements).** Nothing blocks the mathematics:
- The head file elaborates with 0 errors and exactly one sorry warning, `ntime_hierarchy`'s, at
  the base and at the tip (out/17, out/19). It also has 11 new linter warnings (F6).
- The target depends on `[propext, sorryAx, Classical.choice, Quot.sound]`. The only direct
  `sorryAx` user in its closure is `Turing.exists_ndInterpreterCore`. `un_setup` and all 13 new
  privates are within the standard three (out/20).
- The setup is the briefed 8-phase seam chain; `CP = 7|α| + 130` (head 857) and
  `C = CP + CR + 13` (the overlay's `un_universal_of_setup`). The target's body is
  `exact un_universal_of_setup c un_setup`.

What passes:
- integrity: 21/21 internal sums; the bundle's only prerequisite is the base; 7 linear commits;
  the 7 patches = `format-patch` of the bundle's commits; patches = bundle = delivered file
  (blob `8514e6db`, SHA-256 `1f669b22…`);
- scope: the first commit is the overlay byte for byte; overlay → head is exactly the home (b) and
  the body (c); one import (`Build/Rewind`); 13 new `un_` privates; no new public declaration and
  no new public constant (out/56);
- rule 10: a 36-definition seal (every other-file definition reached), with and without the four
  `@[simp]` definitions erased: the body has 0 errors; all 80 controls fail sealed and pass
  unsealed. The worker's 28-name seal, rebuilt from REPORT: 0 body errors, its control fails;
- rule 11; the 95-check probe, 0 errors (base and tip), and in-module;
- the v3 screen: 603 → 616 declarations, 450 → 454 pairs; 4 new, none ≥ 90%; equal to the worker's;
- lint 0 FAIL (the one new WARN is the file size); the 75-module sweep 26 → 25.

Findings (none blocks the mathematics; F1, F2, F5 and F6 are landing edits; F3 and F4 need the user):
- **F1 (scope, an issuance defect; landing edit).** The overlay reverted the frozen docstring of
  `exists_ndAcceptsWithin_decider` (BF) to its text before `b5629b91`, so the head does too.
- **F2 (rule 10, minor; landing edit).** Two coordinate `have`s unfold `FinTM.bufferedCompTM`,
  and two unfold `FinTM.pairExtractTM`'s tape count, through `simp`'s default set. The scripts
  still pass sealed. A 3-line `simp only` repair makes the sealed and unsealed runs identical.
- **F3 (duplication governance; decision).** The brief's "no new cross-file pair" rule is broken
  by two declaration pairs with `ExhaustiveReplay` (59–61%, 54%).
- **F4 (route; decision, accept recommended).** A second private leaf (the guided bank erase), and
  an input rewind proved by its own induction rather than through `FinTM.rewind_heads`.
- **F5 (policy §3 and public-facing text; landing edits).** Three long proofs have no "Proof
  sketch". The home's header carries a campaign label. The module status and the target's own
  docstring are stale.
- **F6 (lint, cosmetic).** 11 new linter warnings: 4 unused `simp` arguments, 7 no-op `push_cast`s.
- **F7 (records, minor).** The seal and axiom logs predate the last two Lean commits. The seal
  source is not shipped. No checkpoint zips. The shared environment logs are not in this zip. The
  branch carries a top-level `evidence/` tree. The probe was not extended. Two small REPORT
  inaccuracies.

## Inputs

| Input | Identity | Evidence |
|---|---|---|
| Zip `exchange/inbox/fill-c1-universal-cont1.zip` | SHA-256 `27ff57c3…cdbdd69` (as given; the session report's). 25 entries, no unsafe entry, CRC OK; copied to `delivery/`, extracted to `delivery/x/`; every member byte-equal to the extraction | out/01, out/02 |
| `SHA256SUMS` | 21/21 OK; covers every file member except itself | out/03 |
| Superseded packaging `5312a4e2…` | not here. Its contents are committed in the branch's `bdeb3309` as `evidence/delivery/item2/`: a bundle with head `f080e469` (pre-wrap), patches 0001–0005, and the final `NTimeHierarchy.lean` (8514e6db). That inconsistency is what the repackage fixed | out/08 |
| Brief `campaign/fills/c1/briefs/c1-fill-universal-cont1.md`, cover `megafill/briefs/megafill-A.md` | read in full at the base `6cfee544` (the dispatch copies were not in the inbox; the attachment hashes are the session report's, unverified here) | — |
| Brief inputs | the overlay (`adf117e1`), the 95-check probe, the 11-file population, the 75-module order list, the base sorry set (26 in 12), the screen base (603/450/123,003) and the pre-ship log, all read at the base | out/10b, out/24, out/36, out/45 |
| Base `6cfee54474e3d954e3395f9d9eab5d025452a8dd` | a records commit; TCSlib = `2ff214c5` (#137's merge). The owned file is blob `5aad1203` at the base, at `2ff214c5` and at the tip | out/15, out/18 |
| Head `d72ed65fec4c920a37be91e88eb0aaad5729d0a1` | the bundle's only ref (`HEAD`), fetched into `refs/review/c1-universal-cont1` | out/04 |
| Snapshots | `oleans-lg4c2` (`c60ed898`'s tree) and `oleans-lu2sc1` (`28150fc1`, #147's head: the tip plus `UniversalK` and the facade). See (b) for exactness | out/15 |
| Campaign tip | `97299639` (`git ls-remote` at 18:5x: unchanged). Open Lean PRs: #149 `lean/spaceused-api` at `097f3e04` (Deterministic, Finite); #147 `lean/u2s-startup-cont1` at `28150fc1` (UniversalK, facade) | out/50 |

Review worktrees, all detached under this folder, each with the `.lake/packages` link (checked
absent first):
- `wt-base`, `wt-ovl` (`de83b80f`, the first edit), `wt-head`;
- `wt-patch` (the base with the 7 patches `git apply`'d) and `wt-tip` (the tip with the owned
  file's diff applied);
- `wt-pr149`, `wt-pr147` (the open PRs' heads; `wt-pr149` also has the file applied);
- `wt-land` (the head with the drafted landing edits).

Lean ran only through `tools/leanelab.sh` (`scripts/elab.sh`), one elaboration at a time; there
was no build or cache command. Both screens ran under `nice -n 10`, each while holding
`locks/screen.lock` (the first launch was lost to the restart while still waiting for the lock and
was relaunched). No delivered file was compiled or run. Probe and seal sources are in `probes/`
and scripts in `scripts/`; the hashes of every probe and script are in out/58.

## (a) Integrity and scope

| # | Check | Result | Evidence |
|---|---|---|---|
| 1 | Bundle | `verify` okay; one ref `HEAD` = `d72ed65f` (REPORT's last commit); sole prerequisite the base | out/04 |
| 2 | Commits | 7, linear, first parent the base; author `C1 fill agent <fill-agent@campaign>`; 09:08:12Z–10:58:17Z (branch created 09:07:40Z; 1 h 51 m of the 3 h budget). Lean: `de83b80f` (first edit), `cec06611`, `460911e9`, `5824c69a`, `f080e469`, `d72ed65f` (style wrap). **Evidence in the tree:** `5824c69a` and `f080e469` also add `evidence/logs/*`, and `bdeb3309` adds only `evidence/` (24 files, 14,553 lines, including a nested bundle). In all, 32 files +18,924/−7, of which the owned file is +1,537/−7 (F7.5) | out/05 |
| 3 | Patch series | the 7 patches apply in order at the base; the 32 resulting files equal the head's blobs. Each patch = `git format-patch --full-index --binary` of its commit, up to abbreviated `index` hashes and the git-version trailer | out/06, out/06b, out/07 |
| 4 | Delivered file | = the head blob `8514e6db` (SHA-256 `1f669b22…`) | out/06 |
| 5 | Final style-wrap commit `d72ed65f` | +24/−13 in the owned file only. The final sweep (10:56Z) already saw the wrapped content (sorry at 1835 = head), so the wrap was in the tree before it was committed | out/05, out/45 |
| 6 | First edit | `de83b80f`'s file = the overlay `NTimeHierarchyOverlay.lean.txt`, byte for byte | out/10b |
| 7 | Regions, overlay → head (`-U0`) | two hunks: 1,420 lines inserted after overlay line 226 (home (b), after `un_universal_of_setup`), and overlay line 282 `  sorry` → `  exact un_universal_of_setup c un_setup` (head 1702). Dropping the home and restoring the `sorry` gives the overlay byte for byte. Region (d) unused | out/10, out/13 |
| 8 | **Base → overlay (F1)** | besides the import and `un_universal_of_setup`, the overlay changes **two passages of BF's docstring** (base 175, 190–194): it re-adds "; spec, fill pending — phase P3.3" and replaces "`E` itself is `Turing.FinNDTM.exists_exhaustiveDecider`, proved (…), so the decider's only open dependency is the universal NDTM" by "Fill obligation, named: `E` itself (…)". This is `8ac94feb`'s text, before the maintainer's `b5629b91` (2026-10-18). `declfreeze` reports `UNAUTHORIZED BODY CHANGE: exists_ndAcceptsWithin_decider` base → overlay and base → head. The pre-ship elaborated the overlay but ran no freeze check on it. The two other overlays issued at this base (R cont2's `NDCodeSimulator`, U2-S cont1's `UniversalK`) are clean | out/10, out/11, out/57 |
| 9 | Freeze (`declfreeze`, `privstmt`, `stmtcheck`, `codeonly`) | public 5 → 5, none added or removed, no statement changed. The target has an authorized body change; BF a docstring change (F1). Private 0 → 14: `un_universal_of_setup` (overlay) + 13 new; none removed or changed. `stmtcheck`'s 19 "missing" lines are its known artifact (it pairs the target's `  sorry` with `ntime_hierarchy`'s); the reversal (row 7) is the exact check | out/11, out/12, out/13 |
| 10 | Imports | 9 → 10: `import TCSlib.Complexity.TuringMachine.Build.Rewind` after the existing imports (region (a), the overlay's). The upstream closure grows 55 → 56 modules, by `Build/Rewind` alone | out/14 |
| 11 | Public constants (workflow.md §4) | the module's public constants are the same 6 at the base and at the head: the 5 public declarations and `ntime_hierarchy_of_pos._proof_1_1`. No derived instance, no new auxiliary | out/56 |
| 12 | Hygiene (1,429 added code lines) | no `sorry`, `admit`, `axiom`, `set_option`, `open`, `section`, `variable`, `attribute`, `native_decide`, `instance`, `deriving`, macro, `#` command, `unfold`, `delta` or `change`. The 4 `decide`s close `some (i : Fin 3) ≠ some 2`. 109 `show`s and 87 `rfl`s expose the file's own lets, its own tables and structure literals; all pass under the seal (rows 22–24) | out/41 |
| 13 | Widths, whitespace | no line of the file over 100 characters (the widest added line is 99); no trailing whitespace, tab or double blank line; `git diff --check` clean | out/40 |
| 14 | Size | 375 → 1,905 lines; 5 public / 14 private (lint INFO) | out/39 |

**The 13 new privates** (head lines; all `un_`, all in the home):
- word facts: `un_flatten` (238), `un_buffer_ge` (245);
- seam steps: `un_step` (255), `un_mapState_comp` (673), `un_step'` (689);
- the header: `un_canon_halt` (277);
- the bank erase: `un_bankAct` (317), `un_bankAct_eq` (322), `un_bankTM` (337), `un_bank_run` (352);
- the input rewind: `un_inRewTM` (575), `un_inRew_run` (587);
- the setup: `un_setup` (723).

REPORT's table lists exactly these, with accurate roles.

## (b) Elaboration and axioms

**Snapshots.** The head's 56-module upstream closure has the same blobs at the base and at
`c60ed898` (`oleans-lg4c2`'s tree), so `lg4c2` is exact for the base. **`Build/InputWindow` is not
in the owned file's upstream closure**, so `lg4c2`'s predating #137's `InputWindow` change does
not matter here. From the base to the tip, two upstream modules change: `Build/StepClock` (#139)
and `ClassNP/ExhaustiveReplay` (#139's merge, #144's docstrings). `28150fc1` (`lu2sc1`) has the
tip's blobs for all 56, so `lu2sc1` is exact for the tip (out/15).

| # | Check | Result | Evidence |
|---|---|---|---|
| 15 | Base file, `lg4c2` | exit 0; `166:8` and `305:8` `declaration uses 'sorry'` only | out/16 |
| 16 | Head file, `lg4c2` | exit 0, 0 errors; `1835:8` (`ntime_hierarchy`) sorry warning; **plus 11 linter warnings** (F6). A sanity copy with `CP := 7·|α| + 1` fails in the ledger, so the elaboration is real | out/17, out/17b |
| 17 | Head file at the tip (`wt-tip` = the tip + the owned file's diff, which applies cleanly and gives blob `8514e6db`), `lu2sc1` | output identical to row 16 | out/18, out/19 |
| 18 | Head file on #149's merged tree (`wt-pr149` + the file, `oleans-lspapi`) | output identical to row 16 | out/54 |
| 19 | Axioms: an in-module copy with 20 prints, an admission walk and a dependency walk | target `[propext, sorryAx, Classical.choice, Quot.sound]`; direct `sorryAx` users in its closure: **`[Turing.exists_ndInterpreterCore]` only**. `un_universal_of_setup`: the same, through the same constant. `un_setup` and the other 12 new privates: within the standard three (4 all three; 6 `propext, Quot.sound`; 2 `propext`; 1 `Quot.sound`), no `sorryAx`. `ntime_hierarchy` and its two corollaries are their own source; `exists_ndAcceptsWithin_decider` goes through the core | out/20 |
| 20 | Other files' privates, equation lemmas | one external private, `_private…UniversalStartup…universalPrefix_start._proof_1`, inside the public statements of `prefixCanon_run`/`_start` (the statement auxiliary the U2-S review also recorded; not a citation). No other file's equation or unfolding lemma | out/20 |
| 21 | TCSlib constants reached (target + 14 privates) | 169. Among them, 36 semireducible, non-projection, non-instance definitions of other files (row 22's seal set); 4 of them `@[simp]` (`Action.apply`, `Cfg.init`, `MultiTapeTM.initCfg`, `NDTM.initCfg`) | out/21, out/22 |

**After item 1's core lands** (its own review; not relied on here). Item 1's REPORT proves
`exists_ndInterpreterCore` modulo two stubs: `exists_replayCanonizer` (NDCodeSimulator) and
`exists_seamLayoutTM`. The second is proved at the tip (#145). So the target's `sorryAx` would then
come only through `Turing.exists_replayCanonizer`, as would BF's (`delivery/item1-report/`). The
hierarchy keeps C1-E's `ntime_hierarchy`.

## (c) Correctness, route and rule 10

I read every new body. Correctness rests on the kernel-checked proof (rows 16–19).

**The construction** (`un_setup`). Let `F := FinTM.pairExtractTM true false` and
`MC := FinTM.bufferedCompTM universalPrefixTM F`.
- **Tapes.** `k := K + MC.k + 1`: the core's `K` under `ι := castSucc ∘ castAdd`, the composite's
  `MC.k` under `ιC := castSucc ∘ natAdd K`, and `cap := Fin.last`.
- **Coordinates.** The buffer is `iBuf` (value `K`). The extractor's bank is
  `Sx := univ.image iEx` (values `K + 1 + e`, `e : Fin F.k`).
- **Phases.** `A1 = embedSilentRetTM ιC cap MC.tm`, `A2 = rewindTM iBuf`, `A3 = clearTM iBuf`,
  `A4 = un_bankTM Sx cap`, `A5 = expandTM iBlkb [true]`, `A6 = rewindTM (ι jR)`, `A7 = clearTM cap`,
  `A8 = un_inRewTM`. They are left-nested `seamCompTM`s; `P := {R8 with q₀ := …}` is read through
  `initCfg_with_q₀`/`runFrom_with_q₀`, and `pexit := inr 2`.
- **Junctions.** Every junction is a literal `Cfg` (`E1`–`E8`), matched field by field with `Cfg.ext`.

| Item (brief route) | Status | Notes |
|---|---|---|
| 1. Header pass, captured, final configuration read | **as briefed** | `un_canon_halt` (`prefixCanon_run`, `prefixCanon_start`, `prefixCanonTM_eq`, `pairExtractTM_fst_run`): first halt at exactly `3|u| + 4 + (4|bt| + 5)`, live before, for every `x`. The endpoint is read through `embedSilentRetTM_run`, `embedSilentCfg_*`, the cast pair and `tapeBlocks_buffer`/`_right`: buffer `bufferTape u` at `2|bt| + 2`, every bank tape `bufferTape bt` at `|bt|`, `cap` `bufferTape bt` at `|bt|`, input head `2|u| + 3`, output `[]`. The frames of `prefixCanon_run` are generalized on obtaining (`∃ fr1 fr2`) |
| 2. The block | **as briefed** | `expandTM_run_ofCfg` with `pat = [true]`, the counter `bits t` on `cap` at head 0 (`counter_cfg_eq`, `counterValue_eq`, `counterValue_bits`): `t` cells of `true` on `ι jR` from 0; the counter left all `true` |
| 3. Cleanup | **refined (F4)** | buffer: `rewindTM` (the brief's sanctioned alternative; `n = |u|`, so `α = []` is covered) and `clearTM`. Bank: **the guided bank erase** `un_bankTM` (F4a), which also rewinds `cap`. Block: `rewindTM`. Counter: `clearTM`. Input: **`un_inRewTM`**, built from `FinTM.controlAction` with its own framed run (F4b) |
| 4. Ledger | **as briefed** | `T = T1 + … + T8 + 7 = 23|bt| + 7|α| + 3t + 46 + counterOverhead bt (t+1) ≤ 25|bt| + 7|α| + 7t + 48` (`counterOverhead_le`), and `|bt| ≤ t` (`length_bits_le_self`), so `T ≤ (7|α| + 130)(t + 1)`. No `|x|` term (the rewind costs `2|u| + 4`). `CP` is chosen after `α`, before `x` and `t` (head 857), as ruling 2 fixes |
| 5. First exit, exit configuration | **as briefed** | each phase's cut is inherited by `seamCompTM_firstReturn_ofCfg` through `un_step`/`un_step'`. The exit is exactly `⟨some pexit, 1, update (fun _ _ => none) (ι jR) blk, fun _ => 0, []⟩` with `blk = bufferTape (replicate t true)`; `blk p ≠ none ↔ 0 ≤ p < t` is proved |
| Edge cases | **covered** | `t = 0`, `x = []` (the input head starts at the right sentinel; the rewind's first left step is unconditional), `α = []` and any `K`, `jR` are instances of the universal statement; no hypothesis restricts them |
| Joins | **as briefed** | R2's `seamCompTM` only; no new host, seam, embedding or parser; no other file's private |

**F4's two refinements.**
- **(a) The bank erase.** `pairExtractTM_fst_run` describes all `F.k` extractor tapes uniformly
  (`fun _ => bufferTape (bits t)`). No published lemma gives `F.k` (no `pairExtractTM_k` at the
  base; the definition, `Build/Primitives.lean` 690–691, says `k := 1`). So the briefed "one
  `clearTM` per scratch word" could only name "the extractor's tape" by unfolding. `un_bankTM S g` is a three-state leaf: one unconditional
  left step, then a left sweep that blanks every tape of the `Finset` `S` while the guide `g` reads
  a symbol, then one step right into a live park. `un_bank_run` proves its exact time `L + 2`, its
  cut and its frames. It reads no other file's private. Its proof reaches other files' definitions
  only through `Action.apply_*`, `step_of_some`, `Cfg.workTapeSymbols_eq` and the `bufferTape`
  lemmas (rows 22–26). It is generic in `S`, so the extractor's tape count never enters **its**
  proof. (But see F2: two of `un_setup`'s coordinate facts do unfold it.)
- **(b) The input rewind.** The brief named `FinTM.rewind_heads`, which gives an existential time
  and no cut. The worker proved the leaf's run directly by a step induction (84 lines). The public
  `FinTM.rewind_scan` gives the scan's exact time, and `ExhaustiveReplay` closes the same leaf with
  `FinTM.timed_rewind` and a first-arrival lemma. So the new proof repeats `rewind_scan`'s
  induction; only the cut is new.

**Rule 10.**

| # | Check | Result | Evidence |
|---|---|---|---|
| 22 | Seal set | the 36 definitions of row 21: `Action.apply`, `Cfg.init`, `.inputSymbol`, `.mapState`, `.workTapeSymbols`, `CodeNDTM.toFinNDTM`, `FinNDTM.AcceptsWithin`, `FinTM.bufferTape`, `.bufferedCompTM`, `.bufferedSecondCfg`, `.controlAction`, `.pairExtractTM`, `.tapeBlocks`, `GuessRunPhase.State`, `MultiTapeTM.initCfg`, `.runFrom`, `.step`, `NDTM.HaltsWithin`, `.initCfg`, `.runWith`, `clearTM`, `counterLoopCfg`, `counterOverhead`, `counterValue`, `embedSilentCfg`, `embedSilentRetTM`, `embedSilentTM`, `expandTM`, `guessRunTM`, `moveInputPos`, `pairEncode`, `prefixCanonTM`, `rewindTM`, `seamCompTM`, `streamStartCfg`, `universalPrefixTM`. The worker's 28 are 27 of these plus the unreached `Cfg.ofWords`. They omit the 9 reached only through `un_universal_of_setup` and the target, which the pre-ship's 9-name seal of that lemma covered (F7.2) | out/22 |
| 23 | Seal S2 (head line 115, `namespace Turing`, to `end Turing` in a section, the 36 `local irreducible`, plus `attribute [-simp]` on the four `@[simp]` definitions), with 40 controls at the top and 40 at the end (one `rfl` per sealed definition, plus a `by simp` control for each of the four) | **body 0 errors**; exactly 80 errors, one per control, none outside a control | out/28-seal-S2*, `probes/UNSealS2.lean.txt` |
| 24 | Seal S1 (no erasure); controls alone, unsealed and sealed | S1: body 0 errors, 72 errors (the 4 `simp` controls pass without the erasure, as expected). Controls unsealed: all 40 pass; sealed alone: all 40 fail | out/28-seal-S1*, out/27-* |
| 25 | The worker's seal (rebuilt from REPORT: 28 names from the home's first line, head 227, to `end Turing`; its control `pairEncode [] [] = [false, true] := rfl`) | body 0 errors; the control fails (1 error) | out/38-seal-worker.out |
| 26 | **Sealed against unsealed routes (F2)** | the used-constant sets of all 16 declarations are identical sealed and unsealed (out/30). The `simp` rewrite traces over the whole module differ in exactly four places. Unsealed, `Fin.cast_eq_self` rewrites `Fin.cast (bufferedCompTM_k …) x` to `x` in `hvjBuf` (780) and `hvjEx` (782); matching it needs `MC.k ≡ universalPrefixTM.k + (1 + F.k)`, an unfolding of `FinTM.bufferedCompTM`. And `Fin.val_eq_zero (a : Fin 1)` rewrites `↑e` for `e : Fin F.k` in `hvjEx` (782) and `hcEx` (960); that needs `F.k ≡ 1`, an unfolding of `FinTM.pairExtractTM`. Sealed, the same scripts go through `Fin.coe_cast` and `Nat.add_left_cancel_iff`. The constant sets do not show it: `Fin.cast_eq_self` (Mathlib, `a.cast rfl = a := rfl`) is an rfl-lemma and leaves no trace, and `Fin.val_eq_zero` (core, `(a : Fin 1) : a.val = 0`) is also used legitimately, on `0 : Fin 1`, in both runs. But the delivered terms type-check only by those unfoldings. The visible symptom is the linter's "`Fin.coe_cast` unused" at 780/782 unsealed (not sealed) | out/29-*, out/30-*, out/31, out/32-* |
| 27 | `rw`/`rwa`/`simp`/`simpa`/`dsimp` arguments (head 227–1702) | 590 occurrences, 154 distinct: 42 TCSlib theorems (published field equations, the cast pair, `tapeBlocks_*`, run/step equations, `counter_cfg_eq`, `length_pairEncode`, `moveInputPos_*`, `prefixCanonTM_eq`); 4 own declarations (`un_bankAct`, `un_bankTM`, `un_inRewTM`, `un_flatten`); 64 locals; 34 Mathlib/core lemmas and simprocs; 10 term arguments (own-table `show … from rfl`, arithmetic `show … by omega`, applications of `embedSilentCfg_cap`/`_unselected`/`un_bankAct_eq`). **No other-file definition.** No `unfold`. The 14 unrestricted `simp`/`simpa` calls are the subject of row 26 | out/42, out/43 |

**Rule 11.**
- No R3 row (`copyTM_run`, `transferTM_run`, `clearTM_run`, `compareTM_run`,
  `incrementTM_run_succ`, `incrementTM_run_overflow`) in the added lines or among the 169 reached
  constants; only `_ofCfg` forms are used.
- No other file's private beyond row 20's statement auxiliary.
- The token hits are false positives: the locals `S`, `T`; prose; `.trans`; and `Cfg.mapState_state`,
  a public theorem.
- Every new private is `un_` (out/44).

## (d) Escalations, probes and promotion candidates

**Escalations: none, and I agree.** No missing lemma was needed for the route as built. F2's
unfoldings are accidental (simp's choice), not a gap: the sealed run shows that the published
lemmas suffice.

| # | Probe | Result | Evidence |
|---|---|---|---|
| 28 | The brief's `C1UniversalCont1ImportProbe` (95 checks), standalone, `lg4c2` | 0 errors, 0 warnings; the output is byte-equal to the worker's `item2-probe.log` and to the pre-ship's `probe.out`. **The worker's probe is the issued one, unextended** | out/24 |
| 29 | The same at the tip, `lu2sc1` | 0 errors; output identical | out/24b |
| 30 | The 95 checks appended to a copy of the head module | 0 errors (the module's 12 warnings only) | out/25 |
| 31 | Citations outside the probe | the 13 new privates use 136 TCSlib constants directly, 69 of them theorems; 33 are in the 95. Outside it: 31 public theorems (among them `Action.apply_inputPos`/`_output`/`_workTapePos`, `Cfg.ext`, `Cfg.inputSymbol_of_zero`, `Cfg.mapState_*`, `Cfg.workTapeSymbols_eq`, `bufferTape_nil`, `bufferedSecondCfg_inputPos`/`_output`/`_state`, `initCfg_with_q₀`, `runFrom_with_q₀`, `runFrom_state_ne_none_of_le`, `runFrom_zero`, `counterOverhead_le`, `counterValue_eq`, `counter_cfg_eq`, `embedSilentCfg_selected_*`/`_state`, `inputSymbolInner`, `length_bits_le_self`, `moveInputPos_*`, `prefixCanon_start`, `seamCompTM_firstReturn_ofCfg`, `universalPrefixTM_k`, `universal_pair_length`) and 5 auxiliaries. All are public at the base (the module elaborates against it; no external private, row 20) (F7.6) | out/26 |

**Promotion candidates** (REPORT's four, and my assessment), for the maintainer's window:
1. **An input rewind with exact time and first-visit cut**, public, in `Simulation` beside
   `rewind_scan`. This is the strongest candidate: it would collapse `un_inRewTM`/`un_inRew_run`,
   `ExhaustiveReplay`'s `xr_inRewindTM` (F3's pair) and U2-S's `ss_inputRewind`/`_run`
   (`UniversalK`, #147): three copies.
2. **A constant-relabelling collapse** `(c.mapState f).mapState (fun _ => e) = c.mapState (fun _ => e)`
   in `StateRenaming` (`un_mapState_comp`). It would remove F3's second pair.
3. **The guided bank erase** (`un_bankTM`/`un_bank_run`), generic in the `Finset`; a catalog-row
   candidate. Alternatively, a published `FinTM.pairExtractTM_k` would let later fills clear the
   extractor's tape by `clearTM`.
4. **The header's first-component pass with its cleanup** (A1–A4) for R's startup and B5a's H1:
   wait for those consumers' briefs to fix its shape. Also `un_step`/`un_step'`, the
   "run + exit + cut" seam package.

**What this unblocks.** BF (`exists_ndAcceptsWithin_decider`) now depends on the core only. C1-E's
X1 (the `ntime_hierarchy` sketch, "waits for UN's integration", backlog) can proceed after landing.

## (e) Duplication and lint

| # | Check | Result | Evidence |
|---|---|---|---|
| 32 | Screen v3 script | SHA-256 `f4feac91…` in `wt-base`, `wt-ovl`, `wt-head`, `wt-tip` and the main checkout | out/35 |
| 33 | Before (the overlay `de83b80f`, the brief's 11-file population) | `603 declarations; 450 pairs; 123,003 chars` (94 s). Equal (comments aside) to the recorded base and to the worker's `item2-screen-before.log` | out/36, out/38 |
| 34 | After (head) | `616; 454; 123,797 chars` (127 s). Equal to the worker's `item2-screen-after.log` | out/37, out/38 |
| 35 | New pairs (`pairdiff.py`, by name, against the before screen and the recorded base) | **4 new, 0 gone**: `un_setup` reproduces `un_mapState_comp` 87% (in-file); `ExhaustiveReplay::xr_inRewindTM` reproduces `un_inRewTM` 61%, and the converse 59%; `ExhaustiveReplay::xr_E_initCfg` reproduces `un_mapState_comp` 54%. **None ≥ 90%. Three directed entries (two declaration pairs) are cross-file with an owned-file declaration on one side (F3)** | out/38 |
| 36 | Known hazards | no pair with `UniversalStartup`, `UniversalK` or `NDCodeSimulator` (`ic_header_capture`), nor with `Primitives`, `Simulation`, `Embed` or `CounterLoop` | out/38 |
| 37 | Discipline | both screens one at a time, `nice -n 10`, under the lock | `scripts/screens.sh`, out/36–37 `.status` |

**The pairs, justified.**
- **`un_setup`/`un_mapState_comp` (87%).** `un_setup`'s `hstart` (head 1530–1576) spells out
  eight-deep `Cfg.mapState_*` rewrite chains, the same field litany that `un_mapState_comp`
  packages. In-file, below 90%.
- **The two cross-file pairs** are the canonical input-rewind leaf shape (unconditional left,
  scan-left-while-some, park) and a five-field `Cfg.ext` over the `Cfg.mapState_*` equations. They
  are not transcriptions (different state types and helpers). But the brief's rule admits **no**
  new cross-file pair (F3). The worker disclosed both. REPORT's "new copies: none" is true of the
  90% threshold, not of the cross-file rule.

| # | Check | Result | Evidence |
|---|---|---|---|
| 38 | Lint, `TCSlib/Complexity/Diagonalization` | base `0 FAIL, 1 WARN over 5 files`; head `0 FAIL, 2 WARN`. The new WARN is `NTimeHierarchy.lean 1905 lines > 1000`, and size alone is no driver (ground rule 8). The head output equals the worker's `evidence/logs/item2-lint.log` | out/39 |
| 39 | Proof sketches (policy §3) | `un_setup` (923 lines) has one, and the overlay's lemma has one. **Missing:** `un_canon_halt` (38 lines), `un_bank_run` (219), `un_inRew_run` (84) (F5). `un_bankAct_eq` has no docstring (private; reviewer discretion) | out/34 |
| 40 | Public-facing text (76 added comment/docstring lines) | one campaign label: the home's header `/-! ### The setup machine's pieces (continuation UN cont1)`, and "reduces target 1" in its first sentence (F5). The `-- phase N:` comments name the machine's phases, which is library vocabulary. No path or date | out/33 |
| 41 | Linter warnings in the head file | 11 new (base 0): unused `simp` arguments at 460, 615 (`Fin.reduceEq`), 662 (`Fin.val_one`), 780 and 782 (`Fin.coe_cast`, F2's symptom); `push_cast` does nothing at 475, 1186, 1400, 1417, 1488, 1491 (F6) | out/17 |

## (f) Environment (addendum v2.4, Parts 1 and 3; shared across the queue)

The shared logs are in item 1's zip (`fill-c1-core-cont2.zip`, `item1/`), not in this one (F7.4).
I read them as data (`delivery/item1-report/`).

| Item | Recorded | Evidence |
|---|---|---|
| Preflight (05:11:11Z) | `nproc` 4. cgroup v1, `memory.limit_in_bytes` 9,223,372,036,854,771,712: no limit, so the headroom is `MemAvailable` 15,975,212 kB = 15.24 GiB ≥ 4. `failcnt` 0, `oom_kill` 0. Disk 26,517,278,720 B = 24.70 GiB ≥ 12 on ext4 (REPORT's "26.5 GB" is decimal). The post-toolchain re-check is 22.29 GiB ≥ 8. **PASS** | `preflight.log` |
| Toolchain | `leanprover/lean4:v4.25.0` via elan; Part 2 did not arise | REPORT |
| Roots | 41. **Byte-equal as a set** to my extraction from the union of the three order lists (118 modules). This item's own list imports 33 directly, as the brief says | out/47 |
| Cache | Lake cloned the manifest's packages and built the cache executable, then `Attempting to download 1023 file(s)`, 1023/1023 downloaded, `Decompressing 1023`, `Completed successfully!`. Unlike megafill B's host, nothing was in the local store beforehand | `cache-get.log`, out/48 |
| Bans | no `lake build` and no unfiltered `lake exe cache get` in this zip's logs or in the shared logs; 1,023 files (against ~7,500 in full) confirm the narrowed fetch | out/48 |
| Disk before this item (Part 3, item 4) | the session report says "21.8 GB before item 2"; **no `df` record is in this zip** (F7.4) | session report |
| Bootstrap (after the first edit, 09:08–09:27Z) | 75/75 in the order list's exact order, 0 errors; **26 sorry warnings in 12 modules = the base set**, by module; `NTimeHierarchy` at 277/415 (the overlay) | out/45 |
| Final sweep (10:42:48–10:56:59Z; `NTimeHierarchy` at 10:56:25Z) | 75/75 in order, 0 errors; **25 in 12** = the base set minus the target. All 350 diagnostics outside `NTimeHierarchy` are identical to the bootstrap's (file, line, column, kind, text). `NTimeHierarchy`'s 12 are row 16's | out/45 |

## (g) Landability

- **The owned file is unchanged from the base to the tip** (blob `5aad1203`). Its history has no
  colleague commit: the maintainer's, and Codex's first UN round (`8449bdd3`). The backlog puts no
  restriction on it besides "one worker per file" (it also holds C1-E's `ntime_hierarchy` stub). No
  open PR or megafill item edits it.
- **At the tip** (row 17) and **on #149's tree** (row 18): identical output.
- **Downstream closure at the tip** (`mkdownmulti`): `Diagonalization/NTimeHierarchy` and the
  `Diagonalization` facade, **2 modules** (out/46). Neither `UniversalK`, `SelfUniversal` nor the
  `TuringMachine` facade is upstream of either (out/49).
- **Overlap with the other landings** (each closure from its own tree, out/50):

  | Landing | Changes | Its closure | Shared with this landing's 2 |
  |---|---|---|---|
  | #149 (`097f3e04`, the space API) | `Deterministic`, `Finite` (two public theorems, no `simp` attribute) | 324 modules (everything downstream of `Deterministic`) | **both** |
  | #147 (`28150fc1`, U2-S cont1) | `UniversalK`, facade | `UniversalK`, `SelfUniversal`, `TuringMachine` | none |
  | Megafill A item 1 (`NDCodeSimulator`) | the core, proved | `NDCodeSimulator`, `NTimeHierarchy`, `Diagonalization`, `TuringMachine` | **both** |
  | Megafill A item 3 (`CodeSimulator`) | the canonizer stage | 10 modules | **both** |

  This landing adds only privates and changes no statement, so #149, item 1 and item 3 see the
  same API. Whichever of them lands second re-elaborates the two modules: a re-replay, not a
  conflict. Item 1's landing changes this target's axiom chain ((b)).

## Decisions for the user

1. **F3: the two cross-file pairs** (`xr_inRewindTM` ↔ `un_inRewTM` 61%/59%;
   `xr_E_initCfg` ← `un_mapState_comp` 54%), against the brief's binding "no new cross-file pair".
   - (a) **Recommended:** accept them as disclosed, record them in the duplication ledger, and
     remove them in the maintainer's window by promotions 1 and 2 of (d). A public rewind leaf with
     a cut would also absorb U2-S's `ss_inputRewind`.
   - (b) Promotions first: a small API PR (the rewind leaf and the `mapState` collapse, each with
     its gate), then this landing rewritten to cite them.
   - (c) Return to a worker for a restructure; a continuation round for two sub-60% pairs.
2. **F4: accept the route refinements.**
   - (a) The guided bank erase: a second private leaf beside the authorized input-rewind leaf. It
     is forced by the unpublished tape count of `pairExtractTM` and is none of rule 7's banned
     kinds. Precedent: U2-S cont1's F1, accepted.
   - (b) The input rewind proved by its own induction instead of through `FinTM.rewind_heads`
     (named by the brief). It re-proves `rewind_scan`'s scan.

   Recommended: accept both; promotion 1 retires (b)'s duplication. Lesson for later briefs: name
   `rewind_scan` + a first-arrival device for the cut, and publish `pairExtractTM_k` or say how to
   clear an abstract bank.
3. **F2: the rule-10 repair at landing.** Recommended: the maintainer's 3-line edit B1–B3 (a
   proof-text change, as the exhaustive replay's landing `b5629b91` did). Alternatively, return it
   to the worker.
4. **F1 and F5: the docstring wording** of the drafted edits (A1–A7). A3 edits the target's frozen
   docstring: the status label and the obligations list become an `**Implementation.**` paragraph,
   as the F5 landing did for the ruler device. Your call.
5. **F6: the optional lint cleanup** (C, 9 lines): in this PR, or leave the warnings.
6. **Process (for the pre-ship checklist):** run `declfreeze` of every overlay against its base
   before issuing (F1).

## Landing

**Not yet clear to merge**: the landing PR is not open, replayed or gated, and decisions 1–2 are
pending. It becomes clear once those are ruled, the PR's base is the campaign branch, its replay
has passed and its fill gate is recorded.

**Land (full): yes**, by a maintainer PR into `complexity/arora-barak-ch3-4`.

**Commits. Do not cherry-pick the series as delivered.** `bdeb3309` (evidence only), and the
`evidence/` parts of `5824c69a` and `f080e469`, would add a top-level `evidence/` tree (24 files,
14,553 lines, a nested bundle) to the library (F7.5).
1. **The fill commit, squashed to the owned file:** on a branch from `97299639`, apply
   `git diff 6cfee544..d72ed65f -- TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean`
   (= `out/18-file-only.patch`; it applies cleanly at the tip and gives blob `8514e6db`). Commit it
   with the author kept (`C1 fill agent <fill-agent@campaign>`) and a public-facing subject, e.g.
   "NTimeHierarchy: the universal NDTM's setup machine, and the universal NDTM proved from the
   interpreter core". Alternatively, cherry-pick `de83b80f`, `cec06611`, `460911e9`, then
   `5824c69a` and `f080e469` with `-n` and `evidence/` dropped, then `d72ed65f`; skip `bdeb3309`.
   The delivered subjects carry campaign labels ("C1 UN cont1 COMPLETE").
2. **The maintainer's edit commit** (`out/53-landedits.diff`, `scripts/landedits.py`, every edit
   asserted; result blob `958751e1`, SHA-256 `562a2a4d…`):
   - **A1 (F1).** BF's docstring is restored to the base's text, then its clause updated: "…so the
     decider's only open dependency is the universal NDTM's interpreter core
     `Turing.exists_ndInterpreterCore`." (out/53b: the only difference from the base).
   - **A2.** Module status: "**Status.** The universal NDTM `Turing.exists_timed_universal_NDTM`
     is proved from the interpreter core `Turing.exists_ndInterpreterCore` (sorried in
     `TCSlib.Complexity.TuringMachine.NDCodeSimulator`); the hierarchy `Complexity.ntime_hierarchy`
     is sorried; the exponential decider and the two corollaries are proved from them."
   - **A3 (decision 4).** The target's docstring:
     - "decision CH34-Q8; spec, fill pending — phase P3.3)" becomes "decision CH34-Q8)";
     - the closing "Fill obligations, named: …" sentence is replaced by "**Implementation.** The
       setup before the guess is one seam chain of eight phases: the prefix canonizer
       `Turing.prefixCanonTM` with the first-component extractor, embedded silently with its
       output `bits t` captured on a scratch tape; the code buffer's rewind and clear; an erase of
       the extractor's scratch tapes that also rewinds the capture; the expansion of `bits t` into
       the unary block (`Turing.expandTM`); the block's rewind; the counter's clear; and the input
       rewind. It first reaches its exit within `(7·|α| + 130)·(t + 1)` steps, with no `|x|` term,
       so the constant is `C = C_P + C_R + 13` with `C_P = 7·|α| + 130` and `C_R` the core's."
   - **A4.** The home's header becomes `/-! ### The setup machine's pieces`, and its first sentence
     "…reduces `Turing.exists_timed_universal_NDTM` to its setup hypothesis."
   - **A5–A7 (F5).** `**Proof sketch.**` paragraphs for `un_canon_halt`, `un_bank_run` and
     `un_inRew_run` (texts in the diff).
   - **B1–B3 (F2).** `hvjBuf` becomes `simp only [jBuf, Fin.coe_cast, Fin.coe_natAdd,
     Fin.coe_castAdd, hup, Fin.val_eq_zero, add_zero]` (here `Fin.val_eq_zero` is applied to
     `0 : Fin 1`). `hvjEx` becomes `simp only [jEx, Fin.coe_cast, Fin.coe_natAdd, hup, zero_add]`.
     `hcEx` becomes `simp only [Fin.coe_natAdd, hup, zero_add]`.
   - **C (F6, optional).** Drop `Fin.reduceEq` at 460 and 615 and `Fin.val_one` at 662; drop the
     seven no-op `push_cast`s.
   - **Checked** (all on `wt-land`):
     - against `lg4c2`: 0 errors and **only `ntime_hierarchy`'s sorry warning** (no linter
       warning), out/51; the same at the tip against `lu2sc1`, out/55;
     - seal S2 on the edited file: body 0 errors, 80/80 controls bite (out/52-LandSealS2*);
     - **the sealed and unsealed `simp` rewrite traces are identical**, 130/130 (out/52);
     - lint 0 FAIL, 2 WARN; no line over 100 characters; public statements unchanged (out/53).
   - Before the gate, re-run the v3 screen on the edited file (expected: the same 4 new pairs; the
     edits touch docstrings and nine short proof lines).
3. **Replay** (link `.lake/packages` in the PR worktree):
   - **If #147 has merged:** the PR's tree is `28150fc1`'s plus this file. Replay the 2 modules
     (`Diagonalization/NTimeHierarchy`, `Diagonalization`) into a copy of `oleans-lu2sc1`. Precheck:
     the Lean diff from `28150fc1` to the PR head is exactly the owned file; the list does not
     contain the root.
   - **If #149 merges first:** replay the closure of everything changed since `28150fc1`
     (`Deterministic`, `Finite`, the owned file): `lspapi`'s 324-module list, from a copy of
     `oleans-lu2sc1`.
   - **If #147 is still open:** the tip differs from `28150fc1` only in `UniversalK` and the
     facade, neither upstream of the 2 modules. A replay into a copy of `lu2sc1` is exact for these
     2 modules, but the snapshot it yields is not the campaign's tree. Prefer to land #147 first.
   - In every case: never compose snapshots.
   - Expected: 0 failures; `NTimeHierarchy` 1 sorry warning (`ntime_hierarchy`); the facade 0; the
     75-module order list 26 → 25.

**Review table for the PR body:**
- integrity: 21/21 sums; bundle (sole prerequisite the base); 7 commits; patches = bundle = file;
- scope: first edit = overlay; home (b) + body (c) only; one import; 13 `un_` privates; no new
  public declaration or constant; BF's docstring restored (F1);
- elaboration, base and tip: 0 errors, `ntime_hierarchy`'s warning only (after C);
- axioms: `sorryAx` only through `exists_ndInterpreterCore`; `un_setup` standard;
- seal: 36 definitions + the simp erasure, 80 controls; the sealed and unsealed routes identical
  after B1–B3;
- probe 95/95 (base, tip, in-module);
- screen 603 → 616 declarations, 450 → 454 pairs, 4 new, none ≥ 90%, two cross-file pairs (F3, as
  ruled);
- lint 0 FAIL; sweep 75/75, 26 → 25.

### F7, the record details
1. `logs/item2-seal*.log` and `logs/item2-axioms.log` were committed at `5824c69a`: a 1,902-line
   file that printed `un_bankAct_wr`/`_mv`, merged into `un_bankAct_eq` by `f080e469`. So REPORT's
   "the delivered file passes sealed" and "axioms clean for every new private" were not evidenced
   on the delivered file. Both hold there (rows 19, 23–25).
2. The worker's seal source (`.lake/axcheck/SealCheck.lean`) is not shipped. It had one control.
   Its name list is in row 22.
3. No checkpoint zips (the brief asks for one per phase). REPORT discloses this; the work finished
   in one arc within budget.
4. The shared logs (preflight, cache-get, cache-probe, mathlib-roots) are not in this zip (Part 3,
   item 2: "copy them into each item's zip"), and there is no `df` record for the disk check before
   this item (Part 3, item 4). The numbers check against item 1's copies ((f)).
5. The branch carries `evidence/` commits (Landing, item 1).
6. The probe was not extended to the 31 further public theorems cited (row 31; all public at the
   base).
7. Two REPORT inaccuracies:
   - "the one line over 100 is the overlay's own, line 118": no line exceeds 100 **characters**;
     that line is over 100 bytes;
   - the ledger line double-counts the counter-overhead term: the bound is
     `25|bt| + 7|α| + 7t + 48 ≤ 32t + 7|α| + 48`, not `+ 50`. Neither affects the proof.
