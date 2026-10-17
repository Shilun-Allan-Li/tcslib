# #118 round-2 gate review: the brief-inventory API, round 3 prepared locally (FAIL 0/1/2)

Reviewer: read-only review sub-agent, 2026-10-17. `$S` is the scratchpad
(`/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad`);
`$G = $S/review/bapi-gate-r2`.

- **Inputs.**
  - The findings `audits/brief-api-r2-findings.md` (SHA-256 `232a9576…bce0`) and the bundle (SHA-256 `901e1fa9…c2bd`), both verified.
  - The Lean is read at #118's round-2 head `4624fc05`.
  - The records come from campaign `00e23bf3`, extracted with `git archive` into `$G/rec/` (drafts, the MIG-12 inventory, the pack, the resolutions, `evidence/brief-api/r2/`).
  - The findings file was read as data.
- **My worktrees** (detached, `.lake/packages` symlinked):
  - `$G/wt`: 4624fc05 with both round-3 patches applied, uncommitted;
  - `$G/wt-base`: 4624fc05, clean.
- **What I did not touch:** the main checkout, `wt-bapi`, `wt-hk` and `wt-m12api`.
- **How Lean ran:** only through `leanelab.sh` against `$S/oleans-lbapi3`, one elaboration at a time. No `lake build`. No commit, push or branch edit.

**Ready to commit locally (round 3, both against 4624fc05):**
- **`$G/r3-repair.patch`** fixes finding 1: the machine model's live-step API.
- **`$G/r3-repair-2.patch`** adds the two laws that the rescan for finding 2 found only privately.

**Ready to run after the local commits: `$G/replay/replay-lbapi4.sh` (320 modules).**

**Not ready to push:** per the user's ruling, round 3 stays local.

## 1. Grades

| # | Auditor | Grade | Verified at 4624fc05 |
|---|---|---|---|
| 1 | major | **ACCEPT, major** | All three obligations are missing under every public name; see §2. The scope is wider than the auditor saw: four more arbitrary-action reads in CfgRecord (§5). |
| 2 | minor | **ACCEPT, minor**, and wider than claimed | The 44-site ledger misses 32 explicit sites and every definitional (implicit) unfolding: 97 implicit (site, definition) pairs at 81 lines in 30 declarations (§5). |
| 3 | minor | **ACCEPT, minor** | MIG-12's API adds 12 names: 4 `Action.liftSymbols` fields, 3 `Cfg.liftSymbols` fields, `incFixed_nil`/`_false_cons`/`_true_cons`/`_length`, and `decFixed_length` (the probe outputs in `drafts/mig12-api/`). Pack line 60 says 13. Round 2 adds 21 + 12 = 33. |

## 2. Finding 1: what exists and what is missing (a)

I searched Configuration, Deterministic and Finite, then the whole library (`grep` and the Lean name table `$G/out/nametable.tsv`).

**Already published:**
- `step_of_halt` and `outputSymbol_of_halt` (halted state only).
- `step_output`: `(tm.step cfg).output = cfg.output ++ (tm.outputSymbol cfg).toList`.
- `workTapePos_step_le` and `workTapePos_apply_le`: bounds only.
- `Action.apply_workTapes` (Simulation, normalized cells).
- `runFrom_zero`, `runFrom_succ_eq_step`, `runFrom_succ_eq_step'`, `runFrom_add`.
- `initCfg_eq`, `Cfg.init_*`.
- `moveInputPos_*`, `Cfg.inputSymbol_of_zero`/`_of_end`, `inputSymbolInner`, `Cfg.workTapeSymbols_eq`.
- `mem_visitedByTapeHead_iff`.

**Missing; no public equivalent under any name:**
- (a) `Action.apply`'s state, input-position, head (`workTapePos`) and output fields. Only the cells and a head bound are public.
- (b) A live-state `step` equation. There is no `step_of_some`, `step_eq` or `step_some` for an arbitrary machine. `Complexity.Meyer.step_eq` is Hydroxyi's, specific to Meyer's `FinTM` setting, and outside CfgRecord's imports. `Simulation.step_eq_of_agreeOn` compares two machines.
- (c) A live-state `outputSymbol` equation.

**The fix: `$G/r3-repair.patch`** (SHA-256 `9a1e1dbf…911d`; 42 insertions; 2 deletions, which are list punctuation in the vendoring headers). It follows #116's precedent for these vendored files:
- **`Configuration.lean`** (Reitwiessner / Bar Natan, vendored):
  - `attribute [simps (config := { isSimp := false }) state inputPos workTapePos output] Action.apply`, directly after the definition, with a `/-! -/` note stating all four formulas.
  - The cells are left to `Simulation`'s `Action.apply_workTapes`. A generated `_workTapes` would clash with it.
  - A vendoring-header bullet and a module-docstring paragraph.
  - Generated names: `Action.apply_state`, `_inputPos`, `_workTapePos` (`= c.workTapePos i + ↑(a.workTapes i).2`) and `_output`.
- **`Deterministic.lean`** (Reitwiessner / Schlesinger, vendored):
  - `MultiTapeTM.step_of_some (h : cfg.state = some q) : tm.step cfg = (tm.tr q cfg.inputSymbol cfg.workTapeSymbols).apply cfg`, beside `step_of_halt`.
  - `MultiTapeTM.outputSymbol_of_some (h : cfg.state = some q) : tm.outputSymbol cfg = (tm.tr q …).output`, beside `outputSymbol_of_halt`.
  - Both are proved by `unfold`/`rw [h]`, as `step_of_halt` is, with formula docstrings.
  - A vendoring-header bullet and a module-docstring paragraph.

No `@[simp]`, no statement changed, every added line ≤ 100 characters (asserted by `review/scripts/bapi_r3_repair.py`).

## 3. The other briefs' primitive readings (b), per brief

The first five rows are judged against each brief's target statement and draft route. I also ran the name-based scan of each owned file (`$G/out/scan-*.tsv`).

| Brief | Primitive readings on its route | Covered? |
|---|---|---|
| **F5** (`exists_rulerHostTM`) | **Yes: the same as MIG-12.** The host performs "the source transition" of an **arbitrary** `M : MultiTapeTM m Bool S` (statement, `InputDevice.lean:313`; draft line 66, "simulation of any native-input machine"). Its proof must read `M.step` at a live state, `Action.apply`'s state, input head (the suppressed left move at the tag), heads, cells and output, a halted step, and `visitedByTapeHead`. | **Only with round 3.** Before it: no live `step` equation and no `Action.apply` head/state/input/output fields. After it: `step_of_some`, `Action.apply_*`, `apply_workTapes`, `step_of_halt`, `moveInputPos_*`, `Cfg.inputSymbol_*`, `step_output`/`outputSymbol_of_some`, `mem_visitedByTapeHead_iff` and the split lemmas cover it. The owned file's existing helpers read `Cfg.inputSymbol` (lines 92, 95), which is already covered. |
| **U2-S** (`exists_selfStartupTMK`) | Its arbitrary machine (the canonizer `E`) is run only through public run lemmas (`prefixCanon_run`, `bufferedSecondCfg_run`, `cleanTM_run`). Primitive readings: `initCfg`/`Cfg.init` (`initCfg_eq`, `Cfg.init_*`, `initCfg_with_q₀`, `runFrom_with_q₀`), `runFrom` (its four lemmas), `spaceUsed` (bounded through `seamCompTM_spaceUsed_le_add`, `spaceUsed_le_mul_succ`). `step`/`Action.apply` appear only for own leaves (`step_of_tapeAction_*`, `step_of_inputMoveAction`, `controlAction_apply`). | Yes. The round-3 lemmas also let own leaves avoid unfolding. |
| **G4** | Own leaves and public rows only; `Action.apply`/`MultiTapeTM.step` are probe-cited for own leaves (the carve-out). No arbitrary machine. | Yes. |
| **F3** | The arbitrary `M` is stepped inside CfgRecord's record row (MIG-12's file), not on F3's route, which composes the window runner and the record lemmas. Its owned file reads `visitedByTapeHead` (WindowClock 79), which is covered. | Yes. |
| **cont6** | Own machines; `step_of_halt`/`outputSymbol_of_halt` are cited. No arbitrary machine. | Yes. |
| *(note)* H1, `exists_uniformSimulator` | CodeSimulator's H1 region (5068–5268, a later brief) already reads an arbitrary `M`'s `step`/`Action.apply`/`initCfg`/`Cfg.init` (lines 5102–5131). | Its brief should cite the round-3 lemmas. |

**Other primitive fields.**
- `spaceUsedByTape`/`spaceUsed` have no definitional equation (only `spaceUsed_eq_spaceUsedOfCfgs` and bounds). No route reads them definitionally, so I did not patch them. Cheap `rfl` lemmas if ever needed.
- `haltsAtStep` is not on any route.
- `Cfg.init`, `initCfg` and `runFrom` are covered.

## 4. Tests (outputs in `$G/out/`, probe sources in `$G/probes/`)

| Check | Result |
|---|---|
| **Configuration** (`probe-Configuration.out`) | exit 0. Its 3 warnings equal the base's (`base-Configuration.out`, shifted 7 lines). The 4 names print the formulas above; axioms `propext`, `Quot.sound`; `simp=false`. The consumer, with `Action.apply` `local irreducible`, reads the head, state, output and input position. |
| **Deterministic** (`probe-Deterministic.out`) | exit 0, 0 warnings (base 0). Both names; axioms `propext`, `Quot.sound`; `simp=false`. The consumer, with `step` and `outputSymbol` irreducible, reads a live step, its emission, and `runFrom c 1`. |
| **CfgRecord consumer** (`consumer-CfgRecord.out`) | exit 0, 0 warnings. `recordStep_window` and `recordStep_observed_action` are re-proved through only the new names, `Action.apply_workTapes` and `Cfg.workTapeSymbols_eq`. `Action.apply`, `MultiTapeTM.step`, `MultiTapeTM.outputSymbol` and `Cfg.workTapeSymbols` are `local irreducible` around both helpers. The six names are declared by hand in the copy, with the patch's exact statements, because their upstream oleans are not built. |
| **Negative control** (`control-CfgRecord.out`) | The original window proof under `Action.apply` irreducible fails at 589/591, as the auditor said. |
| **Patch 2** (`probe-CounterLoop.out`, `probe-Catalog.out`) | CounterLoop: exit 0, 0 warnings (base 0). Catalog: exit 0, 77 warnings, the same multiset as the base. Names, axioms (`propext`, `Quot.sound` / `propext`) and `simp=false` checked. The consumers run with `counterWord` irreducible, and with `scanResult`/`scanKeep`/`scanFold` irreducible. |
| **CfgRecord, the patch-2 sites** (`consumer2-CfgRecord.out`) | exit 0. Line 529 is re-proved by `rw [counterWord_succ, counterWord_zero] at hw` with `counterWord` irreducible. `recordStep_cell_shift`'s zero case is re-proved by `simp only [scanResult_keep_keep, …]` with `scanFold`/`scanKeep` irreducible. The per-definition runs show both originals fail under the same irreducibility. |
| **Freeze** (`freeze-r3.txt`, `freeze-r3-2.txt`) | Configuration 21 → 21 (the four names are attribute-generated). Deterministic 38 → 40 (`step_of_some`, `outputSymbol_of_some`). CounterLoop 57 → 58 (`counterWord_succ`). Catalog 112 → 113 (`scanResult_keep_keep`). `STATEMENT CHANGED: []` everywhere; no body change; nothing removed. |
| **Lint** (`lint-base.txt`, `lint-r3-all.txt`) | 0 FAIL, 67 WARN over 79 files, before and after. Check 8 stays at 151 names. Only the size lines change. |
| **Screens** | See §7. |

**Two notes on patch 2:**
- `counterWord_succ` restates CounterLoop's private `counter_word_succ` (line 494), which its three in-file uses keep using. Retiring the private one is a body edit, left to the maintainer's dedup window.
- `scanResult_keep_keep` is not a copy of the private `scanResult_keep`, which is a different, generic statement.

## 5. Finding 2: the corrected ledger (d)

**The ledger:** `$G/unfold-sites-r3.tsv`, 173 rows. Columns: line, definition, module, kind, mechanism, declaration, in the round-2 ledger, the lemma to re-point to, and source.

**How the rows were found:**
- **Explicit**, 76 rows at 69 lines: `review/scripts/unfold_scan.py`. It reads every tactic argument list (`simp`/`simp only`/`simpa`/`simp_all`/`dsimp`/`simp_rw`/`rw`/`rwa`/`erw`/`nth_rw`/`norm_num`/`field_simp`) as its whole balanced `[...]` across line breaks, plus `unfold`/`delta`. Comments and strings are masked first. Names are resolved against the Lean name table.
  - All 44 round-2 entries are found, plus 32 more:
    - the auditor's 4 in existing categories (`fieldOffset` 2180; `FinTM.bufferTape` 2454, 2601, 2954);
    - the orbit unfoldings at 747/760 (`counterLoopOrbit`, an abbreviation, and `roundOrbit`; 4 rows);
    - the three primitives the round-2 ledger excluded (`Action.apply` 598, `MultiTapeTM.step` 3335, `outputSymbol` 3337);
    - 21 `Cfg.mapState` sites, now re-pointable to #118 round 2's N1 equations.
- **Implicit**, 97 (site, definition) pairs at 81 lines in 30 declarations. These are definitional unfoldings by `change`, `show`, `rfl`, `exact`, `simpa using` and the like.
  - Method: CfgRecord was elaborated with **one** other-module definition `local irreducible` at a time, over 34 candidates (`$G/perdef/`). Each failing site is a site that unfolds that definition.
  - A broad run with all 200 semireducible upstream definitions irreducible (`irred-errors.tsv`, 80 errors) is fully explained by the single-definition runs: 0 unexplained sites.
  - Two limits:
    - It is a lower bound inside a tactic block, which stops at its first failure.
    - Reducible abbreviations (`counterLoopOrbit`, `Cfg.Halted`, …) cannot be made irreducible, so their definitional uses are by design and only their explicit sites are listed.

**Totals by definition.** Explicit / implicit rows:
- `Cfg.mapState` 21 / 26; `Cfg.liftSymbols` 7 / 20; `MultiTapeTM.runFrom` 0 / 16;
- `fieldOffset` 13 / 7; `embedEmitCfg` 5 / 12; `FinTM.bufferTape` 10 / 1;
- `Action.apply` 1 / 6; `decFixed` 4 / 0; `roundOrbit` 2 / 3;
- `Cfg.inputSymbol` 3 / 1; `moveInputPos` 2 / 0; `fieldsTape` 2 / 0; `incFixed` 1 / 1;
- `counterLoopOrbit` 2 / –; `Cfg.workTapeSymbols` 1 / 0; `MultiTapeTM.step` 1 / 0; `MultiTapeTM.outputSymbol` 1 / 0;
- `Cfg.init` 0 / 1; `counterWord` 0 / 1; `scanFold` 0 / 1; `scanKeep` 0 / 1.

**Every row has a published lemma to re-point to, with three exceptions.** These are the hits beyond the auditor's:
- `Action.apply` at 589/591 is the auditor's site. There are **four more arbitrary-action reads**: 1258 (`recordStep_tape_word`), 3764 (`recordStep_position_run`), 4019 and 4120 (`recordStep_apply_run`). All are covered by round 3's `Action.apply_*`.
- **`counterWord`'s successor law is private** (`counter_word_succ`, CounterLoop 494). CfgRecord 529 reads it by `change`. Fixed by patch 2's `counterWord_succ`.
- **The identity scan has no public law.** CfgRecord 1189 uses `scanFold (fun b _ => b) ≡ scanKeep` definitionally, and the private `scanResult_keep` is a different statement. Fixed by patch 2's `scanResult_keep_keep : scanResult scanKeep scanKeep a₀ w = (a₀, w)`.

**`counterLoopTM_run_escape`.**
- **1 direct use**: line 895, in `recordStep_save_run`. Lines 865 and 4313 are docstring mentions.
- Transitive users, through `recordStep_save_run`: `recordStep_save_transport`, `recordStep_prepare_native`, `recordStep_live_native` and `exists_recordStepTM`.
- `recordStep_probe_run` and `recordStep_apply_run` do not use it.

**MIG-12 draft corrections** (for the coordinator):
- Phase 4's table needs:
  - the counts above;
  - rows for `Cfg.mapState` (the N1 equations), `Action.apply` / `MultiTapeTM.step` / `outputSymbol` (round 3), `MultiTapeTM.runFrom` (its four lemmas), `roundOrbit`/`counterLoopOrbit` (`roundOrbit_zero`/`_succ`, through the abbreviation by `exact`/`simp only`), `Cfg.init`, `counterWord` (`counterWord_succ`) and the scans (`scanResult_keep_keep`, `scanResult_*`);
  - a line saying the ledger now includes definitional unfoldings, with the TSV as the binding list.
- Ground rule 10's primitive clause should name `step_of_some`, `outputSymbol_of_some` and `Action.apply_*`.
- Line 139's "3 uses" becomes "1 direct use (`recordStep_save_run`, line 895)".
- The F5 draft's primitive clause (line 204–208) should name the same three groups.

## 6. Replay (e)

- **Closure:** the closure of the four touched files is Configuration's downstream closure. It has **320 modules**, of 743 TCSlib modules; Deterministic, CounterLoop and Catalog are all downstream of it.
- **The list:** produced by `land-g24/scripts/graph2.py` and checked equal for the two-file and four-file landings. It is `$G/replay/down-lbapi4.txt`: topological, root `TCSlib` excluded, every outside import has an olean in `oleans-lbapi3` (PASS).
- **The script:** `$G/replay/replay-lbapi4.sh` (bash syntax-checked), drafted on `replay-lbapi3.sh`'s pattern for a **local** head.
  - Prechecks:
    - a Mathlib build exists;
    - the worktree is clean;
    - the head contains `4624fc05`;
    - the Lean diff from `4624fc05` is exactly the four files, each pinned to its reviewed blob (Catalog `c2802df7…`, CounterLoop `963a97ec…`, Configuration `a9f14a78…`, Deterministic `efd291b1…`). I dry-tested this against my working tree.
    - round 2's replay passed (274/274);
    - the list has 320 modules and no root;
    - `oleans-lbapi4` is absent.
  - It then copies `oleans-lbapi3` to `oleans-lbapi4`, logs to `$S/fills/replay/replay-lbapi4.log`, and writes the static sorry comparison (`api/staticsorry.py`) to `replay-lbapi4-static.txt`.
  - `WT` is `$S/wt-bapi`; edit it if the local commits live elsewhere.

## 7. Screens

Copy-text v3, queued behind the overnight series by `review/scripts/screens_quiet.sh`. It starts only after three quiet checks 20 s apart, then runs one at a time.

**The population** (`$G/screen-pop.txt`, 14 files):
- every file with an `attribute [simps` line;
- Deterministic;
- Catalog.

**Results** (`$G/screen/`), base 4624fc05 vs both patches:
- 798 → 799 declarations screened, 487 → 487 pairs, 139,742 → 139,742 reproduced characters.
- The only changed line is the count. The one newly screened declaration is `scanResult_keep_keep`; the other new bodies are under the 60-character floor. It forms no pair.
- `Action.apply`'s body, now carrying the attribute text, forms no pair either.
- **No new pair.**

## 8. Records for round 3

- **Resolutions:**
  - **F1:** accepted. Fixed by `r3-repair.patch`. CfgRecord's four further arbitrary-action reads are covered too.
  - **F2:** accepted and widened. The corrected ledger is `unfold-sites-r3.tsv`: 76 explicit and 97 implicit rows. Two private-only laws are now published by `r3-repair-2.patch`. The direct use count is 1.
  - **F3:** accepted. Pack erratum: 12 MIG-12 names, 21 other round-2 names, 33 total.
- **The pack's round-3 attestation:** 6 + 2 = 8 new names in round 3. That is 4 generated (`Action.apply_*`) and 4 hand-written (`step_of_some`, `outputSymbol_of_some`, `counterWord_succ`, `scanResult_keep_keep`).
- **Out of scope here:** I did not gate MIG-12's API commit's content beyond the name count.
