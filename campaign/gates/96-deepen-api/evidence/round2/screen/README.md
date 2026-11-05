# Gate 96's copy-text screen (v3), re-run over the pack's cited files (finding 6)

Run on 2026-11-05 by a sub-agent of the cloud maintainer session (text only, under the screen lock)
and reviewed by the maintainer.

## Population (`population.txt`, 32 files)

The 18 files of `evidence/screen/population.txt` (`population-18files.txt`, in its order), then
the 14 files below, each the home of something the pack names, resolved at the repaired head by
declaration search (`git archive` export, `grep` for the declaring line). No basename repeats, so
labels stay `<basename>::<name>` and the new screens compare with the 18-file ones.

| Added file (`TCSlib/Complexity/…`) | What the pack cites there |
|---|---|
| `TuringMachine/Simulation.lean` | `Action.apply_workTapes` (`apply_of_lt`'s proof column) |
| `SpaceComplexity/Machines/ARMLoops.lean` | `AHalt.embed_guardLe` (the block fit). Finding 6 places it in `Machines/ARMProof`; it is declared in `ARMLoops` (line 81), as the supplementary README already says |
| `SpaceComplexity/Machines/ARMProof.lean` | `RegExt` (brief item 1, the register-file equations) |
| `SpaceComplexity/Codec/Langs.lean` | `initLang`, `edgeLang` and the accepting language in `NoEdge`'s and `mem_iff_reach_of_noEdge`'s statements ("the codec's terms") |
| `SpaceComplexity/Savitch.lean` | the general `savitch` (opening line), and the compile and replay lines (`Savitch` 1) |
| `TuringMachine/Nondeterministic.lean` | `NDTM.runWith` (the window seal's controls, brief item 3) |
| `SpaceComplexity.lean` | the facade, which the PR edits (`evidence/freeze/SpaceComplexity-facade.diff`); 0 declarations |
| `SpaceComplexity/Basic.lean` | `SPACE` and `logSpace` (opening line, statements) |
| `SpaceComplexity/NSPACE.lean` | `NSPACE` (opening line) and `FinNDTM.DecidesInSpace` (`N.DecidesInSpace` in the statements) |
| `SpaceComplexity/Codec/Word.lean` | `codeK` (`mem_iff_reach_of_noEdge`'s width hypothesis) |
| `TuringMachine/Encoding.lean` | `pairEncode` (the query layout in brief item 5) |
| `TuringMachine/Build/RecordTable.lean` | the compile and replay lines (`RecordTable` 4) |
| `ClassPSPACE/TQBF.lean` | the replay line (`TQBF` 21) |
| `SpaceComplexity/Hierarchy.lean` | the replay line (`Hierarchy` 4); 0 screened declarations (four, all under 60 characters) |

- **Already in the 18:** every other TCSlib name the pack writes. `Cfg.InWindow` and
  `apply_of_lt` (`CfgRecord`); `Action.apply`, `workTapePos_apply_le` (`Configuration`);
  `Cfg.InWindow.core_bounds`, `NDTM.inWindow_of_coreSum_eq` (`ConfigGraph`); `StepRel`,
  `stepRel_iff_mem`, `mem_of_codePath` (`Codec/Bridge`); `WalkLe`, `walkLe_zero_iff`,
  `reach_iff_walkLe`, `walkLe_short` (`PathWalk`); `RCode`, `WinRun`, `WinRun.snoc`, `winRun_iff`,
  `rcode_iff_reflTransGen`, `rcode_iff`, `coreSum_eq_of_code_eq`, `inWin_runWith_of_decides`,
  `inWin_stepWith`, `mem_iff_of_card_eq`, `winRun_of_card_eq`, `card_rset_succ_of_le`
  (`ExpBFS/Radius`); `Reach`, `reach_of_chain`, `reflTransGen_of_reach`, `mem_iff_reach`
  (`SavitchARM/Reach`); `ISCount.walkLe_succ_iff` (`ISCountMath`); `ISGen.InitM`, `AccM`,
  `mem_ball_iff_rcode` (`ISCountGenRadius`); `Rel` (`Recursion`); `setSt` (`Setup`); `InitO`,
  `AccO`, `outerSt` (`Search`); `Machine`'s `St.*` and the search block `A E`
  (`SavitchARM/Machine`); `stepWith_eq_apply` (`Codec/Step`); `BPLInPCount`'s own `stepRel_iff`
  (the name clash).
  `ISCountMath` and `ExpBFS/Radius` were already present.
- **Not added:** Mathlib names (`Function.update`, `ReflTransGen`, `Nat.bits`, `Iff.rfl`, the
  axioms); `Deepen` and the machine `D`, which exist at neither commit (the fill writes them); the
  ruling's directory scopes `SavitchARM/*`, `Machines/*`, `Codec/*`, which describe ownership and
  cite no file.
- **The earlier supplementary 29-file screen** also had `Machines/ARM`, `ClassNP/NTIME`,
  `SavitchARM/Run` and `ExpBFS/Run`, neighbors the pack does not cite. They are not here; that
  screen (restricted to pairs touching the PR's files) stays as recorded.
- `population-base.txt` (31) is `population.txt` without `SavitchARM/Window.lean`, which does not
  exist at base; `population-head.txt` (32) is `population.txt`.

## Runs

Root: the tree at the commit, exported with
`git -C /home/user/tcslib archive <commit> -- TCSlib | tar -x -C trees/<commit8>`. Command
(`tools/run-screen2.sh.txt`, which holds `$TCSLIB_SCRATCH/locks/screen` for the run):
`nice -n 10 python3 -I copy-text-screen-v3.py <root> $(cat <population>)`, with the script
`scripts/copy-text-screen-v3.py` (blob `2a8df2dc`, the same at both commits), unrestricted.

| Run | Commit | Population | Declarations | Pairs | Characters | Output |
|---|---|---|---|---|---|---|
| base | campaign tip `b325c1ef` (Lean tree = #196's base `4ef99963`; `git diff --stat` empty) | 31 files | 711 | 169 | 41,423 | `screen-base.txt` |
| head | repaired head `f2616fee` | 32 files | 718 | 172 | 41,658 | `screen-head.txt` |

- Both exit 0 with empty stderr (`status.txt`, `*.err`); about 800 s of wall time each on this
  machine (`*.time`).
- **Consistency with the bundled screens:** every one of the 64 base pairs and 65 head pairs of
  the dispatched 18-file screens is in the corresponding 32-file screen. The 105 pairs the wider
  base adds are all among the added files (`Codec/Langs`, `TQBF`, `RecordTable`, `Simulation`,
  …). **None of them touches a file #196 changes.**

**`pairdiff.py screen-head.txt screen-base.txt`** (`pairdiff.txt`): head 172, base 169,
**new at head 3, base-only 0**. Apart from those three lines, the two screens' pair lines are
byte-identical.

```
NEW   CfgRecord.lean::Cfg.InWindow.mono  reproduces  Radius.lean::inWin_mono: 84/93 = 90%
NEW   Radius.lean::inWin_mono  reproduces  CfgRecord.lean::Cfg.InWindow.mono: 84/95 = 88%
NEW   Window.lean::NoEdge  reproduces  Recursion.lean::Rel: 67/79 = 85%
```

Against the dispatched head screen (`89f4ebbc`, 18 files;
`pairdiff-vs-dispatched-head-89f4ebbc.txt`), the only new pairs touching #196's files are the two
`mono` lines. `Cfg.InWindow.mono` is new in the repair commit `f2616fee` (finding 2's harvest). At
`89f4ebbc` the same text sat inline in `apply_of_lt`, where the screen did not see it (it is the
auditor's "`inWin_mono`'s second component verbatim").

## Which of the PR's declarations the screen sees

v3 extracts a declaration's text from its header to the next declaration header it recognizes,
with comments and docstrings stripped, and takes the part after the first `:=` at bracket depth 0
(or from a top-level `|` or `where`). It drops every declaration whose whitespace-free text there
is under 60 characters (`if len(bd) >= 60`) before any comparison, and "declarations screened"
counts only the rest. Two consequences, both read off the code and checked with
`tools/decl-list.py.txt` (which runs v3's own extraction code and compares nothing):

1. **Short bodies are never screened.** `Iff.rfl` is 7 characters. The two register-file
   equations are short proofs: `setSt_toV` 47, `outerSt_toV` 35.
2. **Commands between declarations count toward the preceding body.** `section`, `variable`,
   `end` and the like are not declaration headers. So a new declaration inserted right after an
   old one can shorten the old one's text. `AccO` at base is followed by `section Outer` and
   `variable {s w u v M : ℕ}`, giving 85 characters. The PR puts `accO_iff_orc` between them, so
   `AccO` falls to 56 and drops out. `accO_iff_orc` takes the tail: `Iff.rfl` plus those two lines
   is 36. In the same way `Cfg.inWindow_init` goes from 81 to 72 when `apply_of_lt` follows it,
   but it stays screened.

**The PR's declarations at the repaired head** (base `b325c1ef` → head `f2616fee`;
`decls-base.tsv`, `decls-head.tsv`; v3 body length in characters):

| Declaration | File | Status | v3 body |
|---|---|---|---|
| `Cfg.InWindow.mono` (new) | `CfgRecord` | screened | 95 |
| `Cfg.InWindow.apply_iff` (new; `recordStep_window` made public over any alphabet) | `CfgRecord` | screened | 510 |
| `Cfg.InWindow.apply_of_lt` (new) | `CfgRecord` | screened | 125 |
| `recordStep_observed_action` (changed: cites `apply_iff`) | `CfgRecord` | screened | 902 → 893 |
| `recordStep_window` (removed) | `CfgRecord` | screened at base only | 510 |
| `chain_of_walkLe` (new, private) | `SavitchARM/Reach` | screened | 926 |
| `reach_of_reflTransGen` (new) | `SavitchARM/Reach` | screened | 381 |
| `NoEdge` (new) | `SavitchARM/Window` | screened | 152 |
| `window_reach_of_rcode` (new, private) | `SavitchARM/Window` | screened | 222 |
| `noEdge_of_lt` (new) | `SavitchARM/Window` | screened | 519 |
| `mem_iff_reach_of_noEdge` (new) | `SavitchARM/Window` | screened | 1,363 |
| `window_code_lt` (new, private) | `SavitchARM/Window` | **not screened** | 59 |
| `setSt_toV`, `outerSt_toV` (new) | `Setup`, `Search` | **not screened** | 47, 35 |
| `accO_iff_orc` (new, `Iff.rfl`; 36 with the absorbed `section`/`variable` lines) | `Search` | **not screened** | 36 |
| `stepRel_iff_mem`, `walkLe_zero_iff`, `walkLe_succ_iff_head`, `winRun_iff`, `rcode_iff_reflTransGen`, `rel_iff_orc`, `initO_iff_orc`, `noEdge_iff` (new, `Iff.rfl`) | `Bridge`, `PathWalk`, `Radius`, `Recursion`, `Search`, `Window` | **not screened** | 7 each |
| `AccO` (unchanged; side effect) | `Search` | screened at base, **not at head** | 85 → 56 |
| `Cfg.inWindow_init` (unchanged; side effect) | `CfgRecord` | screened | 81 → 72 |

That is 21 new declarations, one removed, one changed. The screen sees 10 new or changed ones and
loses 2 old ones: `recordStep_window`, renamed into `apply_iff`, and `AccO`. Over the 32 files:
**711 → 718 (+7)**. The facade edit adds no declaration.

## The count discrepancy in finding 6

The finding's two runs, the 12-file run at the five-commit head and the 17-file run at the
eight-commit head, were on the pre-rebase drafts `f6d94afd` and `6134e5dd`. Those commits are not
in the local repository. Their rebased counterparts are #196's fifth commit `46bf218d` and eighth
commit `465f4e66`. Re-run with v3 over the recorded populations, they reproduce the recorded head
screens **byte for byte**, and `cmp` is clean for both (`history/status.txt`):
- `history/screen-46bf218d-12files.txt` equals `round1-12files/screen-head.txt` (273
  declarations, 49 pairs);
- `history/screen-465f4e66-17files.txt` equals `superseded-6134e5dd/screen-head.txt` (323, 64).

So the accounting below is the accounting of the recorded runs. The bases need no stand-in,
since `7a14e855` is local. Over the recorded populations (`history/population-12files.txt`, from
`b0a4f0c9`'s `population.txt`; `history/population-17files.txt`, the bundled
`superseded-6134e5dd/population.txt`), v3's extraction gives (`declaccount/`):


- **Five commits, 270 → 273 (+3):** `Cfg.InWindow.apply_of_lt` (330 characters then),
  `chain_of_walkLe` (634) and `reach_of_reflTransGen` (381). The four `Iff.rfl` equations of those
  commits (`stepRel_iff_mem`, `walkLe_zero_iff`, `winRun_iff`, `rcode_iff_reflTransGen`) are 7
  each. The finding's reading is right: the three non-`Iff.rfl` proofs.
- **Eight commits, 321 → 323 (+2):** the same three (+3), then −1. `setSt_toV` (47) and
  `outerSt_toV` (35) are under the cut-off, as are `rel_iff_orc`, `initO_iff_orc` (7) and
  `accO_iff_orc` (36). `AccO` drops from 85 to 56 because `accO_iff_orc` now sits between it and
  `section Outer`. So the "+2" is not a missed `setSt_toV`/`outerSt_toV` comparison. Neither was
  ever extracted, and one old declaration left the count.
- **Nine commits, 321 → 327:** the eight-commit 323 plus the window module's four
  (`NoEdge` 152, `window_reach_of_rcode` 222, `noEdge_of_lt` 519, `mem_iff_reach_of_noEdge`
  1,363); `window_code_lt` is 59.
- **Repaired head, 18 files: 328** (`declaccount/f2616fee-18files.tsv`). Against `89f4ebbc` it
  adds `mono` and `apply_iff` and removes `recordStep_window`; `apply_of_lt` shrinks 330 → 125 and
  `chain_of_walkLe` grows 634 → 926.

**What this does not show:** a declaration that is never extracted is never compared, in either
direction. The cut-off is v3's design ("at least 60 characters"), but it means the screen says
nothing about the 12 short additions. Nine are `Iff.rfl` restatements of a definition's body
(`accO_iff_orc` included). `setSt_toV`, `outerSt_toV` and `window_code_lt` are short proofs
from published lemmas. The statement-shape grep and the inline sweep (§3) are where such content
is checked.

## Pairs

**Every head pair that touches a file #196 changes** (`pairs-touching-changed-files.txt`, 54 of
the 172; tiles in `tiles-head.txt`). The facade has no declarations, so the files are `CfgRecord`,
`Bridge`, `PathWalk`, `Radius`, `Reach`, `Recursion`, `Search`, `Setup` and `Window`. Three pairs
are new. The other 51 have the same text at base, and neither of their declarations is one #196
adds or changes (`decls-*.tsv`). No pair involves `apply_iff`, `apply_of_lt`, `chain_of_walkLe`,
`reach_of_reflTransGen`, `noEdge_of_lt`, `mem_iff_reach_of_noEdge` or `window_reach_of_rcode`.
That means v3 found nothing reproducing half of them, nor anything they reproduce half of. It does
not mean that nothing re-derives them (see finding 2, whose restructured pairs v3 misses).

Classes:
- **copy:** a re-statement of proved material;
- **idiom:** shared invocation text, not a re-derived fact;
- **already recorded:** a family the records already hold. The ledger itself
  (`campaign/duplication-ledger.md`) holds none of these 54. The records that do are backlog §1
  ARM-2, with its input, the ARM gate's round-2 classified ledger
  (`campaign/fills/arm/evidence/arm-fill/r2/ledger-r2-tables.md`, `classify.tsv`), and gate 64's
  finding 9 with backlog MIG-12-C.

| # | Pair (target reproduces source) | Shared | Class | Reasoning |
|---|---|---|---|---|
| 1 | `CfgRecord.lean::Turing.{k#2` → `CfgRecord.lean::Turing.{k#1` | 66/66 (100%) | already recorded | two private instances (`Fintype`, `DecidableEq`) of `recordStepPhase` with the same `rcases`/`cases`/`infer_instance` body; one of `CfgRecord`'s 28 in-file pairs, the same 28 by name as gate 64's reviewed screen (finding 9; backlog MIG-12-C, the reader compression) |
| 2 | `CfgRecord.lean::Turing.{k#1` → `CfgRecord.lean::Turing.{k#2` | 66/66 (100%) | already recorded | two private instances (`Fintype`, `DecidableEq`) of `recordStepPhase` with the same `rcases`/`cases`/`infer_instance` body; one of `CfgRecord`'s 28 in-file pairs, the same 28 by name as gate 64's reviewed screen (finding 9; backlog MIG-12-C, the reader compression) |
| 3 | `Radius.lean::coreSum_eq_of_code_eq` → `BPLInPCount.lean::coreSum_eq_of_code_eq` | 65/65 (100%) | copy (pre-existing) | The same public lemma, statement and one-line proof, in `Complexity.ExpBFS` (`Radius`) and `Randomized.BPLInP` (`BPLInPCount`), both from `b068e238`. #196 changes neither, and cites the `ExpBFS` one. Not in the ledger or the ARM gate's (whose population had no `BPLInPCount`) |
| 4 | `BPLInPCount.lean::coreSum_eq_of_code_eq` → `Radius.lean::coreSum_eq_of_code_eq` | 65/65 (100%) | copy (pre-existing) | The same public lemma, statement and one-line proof, in `Complexity.ExpBFS` (`Radius`) and `Randomized.BPLInP` (`BPLInPCount`), both from `b068e238`. #196 changes neither, and cites the `ExpBFS` one. Not in the ledger or the ARM gate's (whose population had no `BPLInPCount`) |
| 5 | `Recursion.lean::tail1F` → `Recursion.lean::tail0F` | 352/363 (97%) | already recorded | ARM-2 (b), family K14 (the Savitch recursion tails), acknowledged scope A2b; ARM gate round-2 ledger S121 |
| 6 | `Recursion.lean::tail0F` → `Recursion.lean::tail1F` | 352/363 (97%) | already recorded | ARM-2 (b), family K14 (the Savitch recursion tails), acknowledged scope A2b; ARM gate round-2 ledger S121 |
| 7 | `Recursion.lean::tail0F` → `Recursion.lean::tail1T` | 223/233 (96%) | already recorded | ARM-2 (b), family K14 (the Savitch recursion tails), acknowledged scope A2b; ARM gate round-2 ledger S120 |
| 8 | `Bridge.lean::mem_of_codePath` → `Radius.lean::coreSum_eq_of_code_eq` | 60/65 (92%) | idiom | the one-line `coreSum_eq_of_cfgWord_eq … bits_cfgCode` step inside a longer proof; `Bridge` is below `Radius`. Against `Radius`, ARM gate round-2 ledger I031 (IC24): incidental |
| 9 | `Bridge.lean::mem_of_codePath` → `BPLInPCount.lean::coreSum_eq_of_code_eq` | 60/65 (92%) | idiom | the one-line `coreSum_eq_of_cfgWord_eq … bits_cfgCode` step inside a longer proof; `Bridge` is below `Radius`. Against `Radius`, ARM gate round-2 ledger I031 (IC24): incidental |
| 10 | `Recursion.lean::tail1F` → `Recursion.lean::tail1T` | 211/233 (91%) | already recorded | ARM-2 (b), family K14 (the Savitch recursion tails), acknowledged scope A2b; ARM gate round-2 ledger S122 |
| 11 | `CfgRecord.lean::Cfg.InWindow.mono` → `Radius.lean::inWin_mono` | 84/93 (90%) | **copy** | NEW. The same proof term; `ExpBFS.inWin_mono` is the specialization to `N`'s configurations. #196 adds the general form beside `Cfg.InWindow`, where backlog ARM-1 (D1) and the ARM payback notes §7 (a follow-up the user accepted) put it, but leaves `inWin_mono` (3 uses in `Radius`). Not in the ledger |
| 12 | `Search.lean::outerV_run` → `Search.lean::outerSt_bd` | 63/70 (90%) | idiom | the `simp only [St.Bd, outerSt, setSt, St.zero]` and `size_facts` invocations; ARM gate round-2 ledger S129: incidental |
| 13 | `Radius.lean::inWin_mono` → `CfgRecord.lean::Cfg.InWindow.mono` | 84/95 (88%) | **copy** | NEW. The same pair, read the other way |
| 14 | `CfgRecord.lean::recordStep_reject_run` → `CfgRecord.lean::recordStep_empty_run` | 477/551 (87%) | already recorded | phase-run and contract-reader plumbing (`recordStep_phase_run`, `recordStep_contract_clauses`, snapshot `simp` sets); one of `CfgRecord`'s 28 in-file pairs, the same 28 by name as gate 64's reviewed screen (finding 9; backlog MIG-12-C, the reader compression) |
| 15 | `CfgRecord.lean::recordStep_empty_run` → `CfgRecord.lean::recordStep_reject_run` | 477/557 (86%) | already recorded | phase-run and contract-reader plumbing (`recordStep_phase_run`, `recordStep_contract_clauses`, snapshot `simp` sets); one of `CfgRecord`'s 28 in-file pairs, the same 28 by name as gate 64's reviewed screen (finding 9; backlog MIG-12-C, the reader compression) |
| 16 | `Window.lean::NoEdge` → `Recursion.lean::Rel` | 67/79 (85%) | idiom | NEW. The shared text is the query layout `pairEncode x (pairEncode (Nat.bits u) … (Nat.bits s))`; `NoEdge` restates none of `Rel`'s meaning (the pack's disposition; the auditor's note 11 agrees; the user's ruling on the exclusion is still to be recorded) |
| 17 | `CfgRecord.lean::recordStep_contract_clauses` → `CfgRecord.lean::recordStep_contract_clauses_range` | 122/145 (84%) | already recorded | phase-run and contract-reader plumbing (`recordStep_phase_run`, `recordStep_contract_clauses`, snapshot `simp` sets); one of `CfgRecord`'s 28 in-file pairs, the same 28 by name as gate 64's reviewed screen (finding 9; backlog MIG-12-C, the reader compression) |
| 18 | `CfgRecord.lean::recordStep_copyback_run` → `CfgRecord.lean::recordStep_reject_run` | 462/557 (83%) | already recorded | phase-run and contract-reader plumbing (`recordStep_phase_run`, `recordStep_contract_clauses`, snapshot `simp` sets); one of `CfgRecord`'s 28 in-file pairs, the same 28 by name as gate 64's reviewed screen (finding 9; backlog MIG-12-C, the reader compression) |
| 19 | `CfgRecord.lean::recordStep_position_run` → `CfgRecord.lean::recordStep_reject_run` | 436/557 (78%) | already recorded | phase-run and contract-reader plumbing (`recordStep_phase_run`, `recordStep_contract_clauses`, snapshot `simp` sets); one of `CfgRecord`'s 28 in-file pairs, the same 28 by name as gate 64's reviewed screen (finding 9; backlog MIG-12-C, the reader compression) |
| 20 | `CfgRecord.lean::recordStep_probe_run` → `CfgRecord.lean::recordStep_runFrom_one` | 73/95 (77%) | already recorded | the probe run cites `recordStep_runFrom_one` (RO-1's `CfgRecord` member) and steps once more by `runFrom_succ_eq_step'`, with no re-derivation; one of `CfgRecord`'s 28 in-file pairs, the same 28 by name as gate 64's reviewed screen (finding 9; backlog MIG-12-C, the reader compression) |
| 21 | `Recursion.lean::desc2` → `Recursion.lean::tail0F` | 273/363 (75%) | already recorded | ARM-2 (b), family K14 (the Savitch recursion tails), acknowledged scope A2b; ARM gate round-2 ledger S117 |
| 22 | `Recursion.lean::desc2` → `Recursion.lean::tail1F` | 272/363 (75%) | already recorded | ARM-2 (b), family K14 (the Savitch recursion tails), acknowledged scope A2b; ARM gate round-2 ledger S119 |
| 23 | `PathWalk.lean::walkLe_reach` → `ISCountMath.lean::walkLe_lt` | 79/106 (75%) | idiom | the `induction j generalizing c` skeleton; ARM gate round-2 ledger I077: incidental |
| 24 | `Recursion.lean::desc1` → `Recursion.lean::Inv.setM` | 67/91 (74%) | idiom | the register-invariant tuple `⟨h.hn, h.ha, …⟩` or the `step_of`/`regs` run steps; ARM gate round-2 ledger S123: incidental |
| 25 | `CfgRecord.lean::recordStep_halt_run` → `CfgRecord.lean::recordStep_reject_run` | 393/557 (71%) | already recorded | phase-run and contract-reader plumbing (`recordStep_phase_run`, `recordStep_contract_clauses`, snapshot `simp` sets); one of `CfgRecord`'s 28 in-file pairs, the same 28 by name as gate 64's reviewed screen (finding 9; backlog MIG-12-C, the reader compression) |
| 26 | `CfgRecord.lean::recordStep_restore_native` → `CfgRecord.lean::recordStep_empty_run` | 380/551 (69%) | already recorded | phase-run and contract-reader plumbing (`recordStep_phase_run`, `recordStep_contract_clauses`, snapshot `simp` sets); one of `CfgRecord`'s 28 in-file pairs, the same 28 by name as gate 64's reviewed screen (finding 9; backlog MIG-12-C, the reader compression) |
| 27 | `CfgRecord.lean::recordStep_contract_clauses_range` → `CfgRecord.lean::recordStep_contract_clauses` | 122/177 (69%) | already recorded | phase-run and contract-reader plumbing (`recordStep_phase_run`, `recordStep_contract_clauses`, snapshot `simp` sets); one of `CfgRecord`'s 28 in-file pairs, the same 28 by name as gate 64's reviewed screen (finding 9; backlog MIG-12-C, the reader compression) |
| 28 | `CfgRecord.lean::recordStep_map_snapshot` → `CfgRecord.lean::recordStep_clear_snapshot` | 1037/1506 (69%) | already recorded | phase-run and contract-reader plumbing (`recordStep_phase_run`, `recordStep_contract_clauses`, snapshot `simp` sets); one of `CfgRecord`'s 28 in-file pairs, the same 28 by name as gate 64's reviewed screen (finding 9; backlog MIG-12-C, the reader compression) |
| 29 | `Recursion.lean::desc2` → `Recursion.lean::Inv.setM` | 62/91 (68%) | idiom | the register-invariant tuple `⟨h.hn, h.ha, …⟩` or the `step_of`/`regs` run steps; ARM gate round-2 ledger S124: incidental |
| 30 | `Recursion.lean::desc2` → `Recursion.lean::tail1T` | 157/233 (67%) | idiom | the register-invariant tuple `⟨h.hn, h.ha, …⟩` or the `step_of`/`regs` run steps; ARM gate round-2 ledger S118: incidental |
| 31 | `CfgRecord.lean::recordStep_halt_run` → `CfgRecord.lean::recordStep_empty_run` | 365/551 (66%) | already recorded | phase-run and contract-reader plumbing (`recordStep_phase_run`, `recordStep_contract_clauses`, snapshot `simp` sets); one of `CfgRecord`'s 28 in-file pairs, the same 28 by name as gate 64's reviewed screen (finding 9; backlog MIG-12-C, the reader compression) |
| 32 | `CfgRecord.lean::recordStep_position_run` → `CfgRecord.lean::recordStep_empty_run` | 363/551 (66%) | already recorded | phase-run and contract-reader plumbing (`recordStep_phase_run`, `recordStep_contract_clauses`, snapshot `simp` sets); one of `CfgRecord`'s 28 in-file pairs, the same 28 by name as gate 64's reviewed screen (finding 9; backlog MIG-12-C, the reader compression) |
| 33 | `Bridge.lean::mem_iff_codeChain` → `Radius.lean::inWin_runWith_of_decides` | 380/581 (65%) | already recorded | ARM-2 (b), family K9 ("`mem_iff_codeChain` re-derives the window argument of `ExpBFS.inWin_runWith_of_decides`. Factoring: cite."), acknowledged scope A2b; ARM gate round-2 ledger I032 |
| 34 | `CfgRecord.lean::recordStep_copyback_run` → `CfgRecord.lean::recordStep_empty_run` | 348/551 (63%) | already recorded | phase-run and contract-reader plumbing (`recordStep_phase_run`, `recordStep_contract_clauses`, snapshot `simp` sets); one of `CfgRecord`'s 28 in-file pairs, the same 28 by name as gate 64's reviewed screen (finding 9; backlog MIG-12-C, the reader compression) |
| 35 | `CfgRecord.lean::recordStep_probe_run` → `CfgRecord.lean::recordStep_read_run` | 91/147 (62%) | already recorded | phase-run and contract-reader plumbing (`recordStep_phase_run`, `recordStep_contract_clauses`, snapshot `simp` sets); one of `CfgRecord`'s 28 in-file pairs, the same 28 by name as gate 64's reviewed screen (finding 9; backlog MIG-12-C, the reader compression) |
| 36 | `Recursion.lean::tail1T` → `Recursion.lean::tail0F` | 223/363 (61%) | already recorded | ARM-2 (b), family K14 (the Savitch recursion tails), acknowledged scope A2b; ARM gate round-2 ledger S120 |
| 37 | `Search.lean::outerSt_inv` → `Recursion.lean::pushP_lt` | 70/114 (61%) | idiom | the shared text is a `variable` line and `open Classical in`, commands v3 counts into the preceding bodies; ARM gate round-2 ledger I103: incidental |
| 38 | `CfgRecord.lean::recordStep_restore_digits` → `CfgRecord.lean::recordStep_clear_heads` | 123/208 (59%) | already recorded | phase-run and contract-reader plumbing (`recordStep_phase_run`, `recordStep_contract_clauses`, snapshot `simp` sets); one of `CfgRecord`'s 28 in-file pairs, the same 28 by name as gate 64's reviewed screen (finding 9; backlog MIG-12-C, the reader compression) |
| 39 | `CfgRecord.lean::recordStep_prepare_native` → `CfgRecord.lean::recordStep_clear_heads` | 123/208 (59%) | already recorded | phase-run and contract-reader plumbing (`recordStep_phase_run`, `recordStep_contract_clauses`, snapshot `simp` sets); one of `CfgRecord`'s 28 in-file pairs, the same 28 by name as gate 64's reviewed screen (finding 9; backlog MIG-12-C, the reader compression) |
| 40 | `CfgRecord.lean::recordStep_read_prefix` → `CfgRecord.lean::recordStep_clear_snapshot` | 889/1506 (59%) | already recorded | phase-run and contract-reader plumbing (`recordStep_phase_run`, `recordStep_contract_clauses`, snapshot `simp` sets); one of `CfgRecord`'s 28 in-file pairs, the same 28 by name as gate 64's reviewed screen (finding 9; backlog MIG-12-C, the reader compression) |
| 41 | `CfgRecord.lean::recordStep_map_snapshot` → `CfgRecord.lean::recordStep_scan_preserves` | 339/578 (59%) | already recorded | phase-run and contract-reader plumbing (`recordStep_phase_run`, `recordStep_contract_clauses`, snapshot `simp` sets); one of `CfgRecord`'s 28 in-file pairs, the same 28 by name as gate 64's reviewed screen (finding 9; backlog MIG-12-C, the reader compression) |
| 42 | `Recursion.lean::tail1T` → `Recursion.lean::tail1F` | 211/363 (58%) | already recorded | ARM-2 (b), family K14 (the Savitch recursion tails), acknowledged scope A2b; ARM gate round-2 ledger S122 |
| 43 | `ISCountGenRadius.lean::mem_iff_exists_acc_of_card_eq` → `Radius.lean::mem_iff_of_card_eq` | 152/263 (58%) | idiom | the acceptance unpacking and `rcode_iff`/`mem_acceptLang` closing; ARM gate round-2 ledger I063: incidental |
| 44 | `ISCountMath.lean::walkLe_succ_iff` → `PathWalk.lean::walkLe_succ` | 70/122 (57%) | idiom | the induction skeleton and the `Or.inl`/`Or.inr` cases; ARM gate round-2 ledger I078: incidental |
| 45 | `CfgRecord.lean::recordStep_clear_snapshot` → `CfgRecord.lean::recordStep_map_snapshot` | 1037/1814 (57%) | already recorded | phase-run and contract-reader plumbing (`recordStep_phase_run`, `recordStep_contract_clauses`, snapshot `simp` sets); one of `CfgRecord`'s 28 in-file pairs, the same 28 by name as gate 64's reviewed screen (finding 9; backlog MIG-12-C, the reader compression) |
| 46 | `CfgRecord.lean::RecordEqIndex` → `CfgRecord.lean::RecordTestIndex` | 73/129 (57%) | already recorded | two `inductive` index types sharing constructors and `deriving DecidableEq, Fintype`; one of `CfgRecord`'s 28 in-file pairs, the same 28 by name as gate 64's reviewed screen (finding 9; backlog MIG-12-C, the reader compression) |
| 47 | `CfgRecord.lean::recordStep_read_fields` → `CfgRecord.lean::recordStep_write_back` | 1699/3028 (56%) | already recorded | phase-run and contract-reader plumbing (`recordStep_phase_run`, `recordStep_contract_clauses`, snapshot `simp` sets); one of `CfgRecord`'s 28 in-file pairs, the same 28 by name as gate 64's reviewed screen (finding 9; backlog MIG-12-C, the reader compression) |
| 48 | `Recursion.lean::desc1` → `Recursion.lean::tail1T` | 129/233 (55%) | idiom | the register-invariant tuple `⟨h.hn, h.ha, …⟩` or the `step_of`/`regs` run steps; ARM gate round-2 ledger S116: incidental |
| 49 | `CfgRecord.lean::RecordTestIndex` → `CfgRecord.lean::RecordEqIndex` | 73/133 (55%) | already recorded | two `inductive` index types sharing constructors and `deriving DecidableEq, Fintype`; one of `CfgRecord`'s 28 in-file pairs, the same 28 by name as gate 64's reviewed screen (finding 9; backlog MIG-12-C, the reader compression) |
| 50 | `CfgRecord.lean::recordStep_read_prefix` → `CfgRecord.lean::recordStep_copyback_run` | 1276/2377 (54%) | already recorded | phase-run and contract-reader plumbing (`recordStep_phase_run`, `recordStep_contract_clauses`, snapshot `simp` sets); one of `CfgRecord`'s 28 in-file pairs, the same 28 by name as gate 64's reviewed screen (finding 9; backlog MIG-12-C, the reader compression) |
| 51 | `CfgRecord.lean::recordStep_restore_native` → `CfgRecord.lean::recordStep_reject_run` | 292/557 (52%) | already recorded | phase-run and contract-reader plumbing (`recordStep_phase_run`, `recordStep_contract_clauses`, snapshot `simp` sets); one of `CfgRecord`'s 28 in-file pairs, the same 28 by name as gate 64's reviewed screen (finding 9; backlog MIG-12-C, the reader compression) |
| 52 | `CfgRecord.lean::recordStep_copyback_run` → `CfgRecord.lean::recordStep_clear_heads` | 106/208 (51%) | already recorded | phase-run and contract-reader plumbing (`recordStep_phase_run`, `recordStep_contract_clauses`, snapshot `simp` sets); one of `CfgRecord`'s 28 in-file pairs, the same 28 by name as gate 64's reviewed screen (finding 9; backlog MIG-12-C, the reader compression) |
| 53 | `CfgRecord.lean::recordStep_state_run` → `CfgRecord.lean::recordStep_scan_preserves` | 290/578 (50%) | already recorded | phase-run and contract-reader plumbing (`recordStep_phase_run`, `recordStep_contract_clauses`, snapshot `simp` sets); one of `CfgRecord`'s 28 in-file pairs, the same 28 by name as gate 64's reviewed screen (finding 9; backlog MIG-12-C, the reader compression) |
| 54 | `Setup.lean::pw_run` → `Setup.lean::ld_run` | 190/380 (50%) | idiom | the `St.Bd` bound step and the `reach_of_eq`/`AReach.refl` closing steps; ARM gate round-2 ledger S130: incidental |

**Summary: 2 copy pairs (one copy), 2 pre-existing copy pairs (one copy), 13 idiom, 37 already
recorded.**
- **The new copy:** `Turing.Cfg.InWindow.mono` (new, public, `CfgRecord`) and
  `Complexity.ExpBFS.inWin_mono` (public, `Radius:65`) have the same proof term
  (`⟨fun i => (h.1 i).trans …, fun i z hz => h.2 i z (lt_of_le_of_lt …)⟩`). `inWin_mono` is
  the instance at `N`'s configurations. Moving it beside `Cfg.InWindow` was recorded as a follow-up
  the user accepted (ARM payback `LANDING-NOTES.md` §7; backlog ARM-1, D1). #196 creates the
  target, so the copy now exists in the tree. It sits within finding 2's window-step kind (the
  auditor cites `inWin_mono`'s component). Under WORKFLOW §3 it is a major unless that kind is
  acknowledged. **Disposition (the maintainer, 2026-11-05):** that kind is acknowledged. The user
  acknowledged the window-step family by kind (WS-1, `campaign/duplication-ledger.md`) and widened
  it the same day; `inWin_mono` is a named member, paid back in the 12.2c window. No change to
  `Radius` in this PR.
- **The pre-existing copy** `coreSum_eq_of_code_eq` (`Radius` ⇄ `BPLInPCount`) is not #196's.
  Neither declaration changed, and the pair is at base. Recorded as CE-1 (acknowledged by the
  user for 12.2c, 2026-11-05), not as a gate-96 item.
- **The search is candidate enumeration plus inspection:** the screen lists pairs over a
  threshold, and each listed pair was read through its tiles. It is not exhaustive. Short
  declarations are not extracted (see above), and restructured re-derivations fall under the
  threshold (finding 2).

## Files

- `population.txt` (32), `population-base.txt` (31), `population-head.txt` (32),
  `population-18files.txt` (the bundled 18)
- `screen-base.txt`, `screen-head.txt` (each with `.time` and `.err`), `status.txt`
- `pairdiff.txt` (`pairdiff.py screen-head.txt screen-base.txt`);
  `pairdiff-vs-dispatched-head-89f4ebbc.txt` (`pairdiff.py screen-head.txt` against the bundled
  `evidence/screen/screen-head.txt`)
- `pairs-touching-changed-files.txt`: the 54 head pairs classified above
- `decls-base.tsv`, `decls-head.tsv`: every declaration v3's extractor sees over the 32 files,
  `screened` or `short`, with its v3 body length and hashes
- `declaccount/`: the same at the earlier heads, over the populations recorded then
- `history/`: the reproductions of the recorded five- and eight-commit head screens, with their
  populations, `.time`/`.err` and `status.txt`
- `driver.log`: the detached driver's log of the two runs (lock waits, exit lines)
- Trees: `../trees/<commit8>/` (`git archive` exports); tools: `../tools/` (`run-screen2.sh`,
  `decl-list.py`, `pairtiles.py`, the v3 copy, `gate96-driver.sh`)
- `tiles-head.txt`: the shared tiles of the head pairs classified above (`tools/pairtiles.py.txt`:
  v3's own `lcs` and tiling, on listed pairs only)
