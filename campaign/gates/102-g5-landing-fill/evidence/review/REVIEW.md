# Review of fill delivery u2s-g5 (`Turing.FinTM.two_work_tapes_run`)

Delivered head `deliver/fill-u2s-g5-in` = `71046be0` on base `335d31d4`; only
`TCSlib/Complexity/TuringMachine/Robustness/TwoTapes.lean` changes (86 → 2,464 lines). Line
numbers below are the delivered file's (`TT:<n>`) unless stated. Read-only review; the tracked
files are untouched.

## Verdict

**The claim holds.** `two_work_tapes_run` is proved with its frozen statement, on
`[propext, Classical.choice, Quot.sound]`. I checked this independently: I elaborated the
delivered sealed copy plus `#print axioms` (elaboration 1, `elab1-sealed.out`). It gave exit 0, no
diagnostic at all, and the three standard axioms for the target and for `two_work_tapes_binary`.

- **Blockers:** none.
- **Majors:** 2, both duplication.
  - One is trivial to fix before landing (F1).
  - One is forced by the import rule and needs human acknowledgment (F2).
- **Minors and notes:** evidence and accounting gaps, listed below.

I could not reproduce `universal_TlogT`'s axioms, because my snapshot holds the base `TwoTapes`.
It follows from the target's prints and gate 92's analysis.

## Findings

| # | Sev. | Where | Finding | Fix |
|---|---|---|---|---|
| F1 | **major** | TT:1422–1424 `tt_output_map` | It restates core `Option.toList_map` (`Init/Data/Option/List.lean:67`, always imported): `(o.map f).toList = o.toList.map f`. Elaboration 2 closes the private's exact statement with `:= Option.toList_map`. It is outside every acknowledged family, so the brief (Duplication governance) makes it a major. It was also never posed to `exact?`, although it is one of only 7 privates whose statement mentions no `tt_` definition. So REPORT §7's "those whose statements use only library notions were posed to `exact?`" is false. | Delete the private. Rewrite with `Option.toList_map` at TT:1478 and TT:1523. Re-run the seal and the screen. The debt then disappears. |
| F2 | **major** (human ack) | TT:2319–2323 `tt_sum_range_fin` | It restates Mathlib's `Finset.sum_range` / `Fin.sum_univ_eq_sum_range`. Elaboration 2 confirms that these, and `Finset.sum_fin_eq_sum_range` and `Fin.map_valEmbedding_univ`, are unknown constants in the closure, so the copy is forced by "no other import". The delivery grades it an "accounting minor", but no acknowledged family covers it, so by the brief's rule it is a major. REPORT §7 also says "New copies: none" while disclosing it. | The maintainer acknowledges it and names a resolution: at integration, import `Mathlib.Algebra.BigOperators.Fin` and cite `Finset.sum_range`. Correct REPORT §7. |
| F3 | minor | `evidence/logs/final/inspection.md` | **The table is incomplete.** Its extractor is line-based. It drops about 50 arguments of rewrite lists that span several lines: TT:544, 1146, 1153, 1216–1222, 1268, 1301, 1312, 1795, 1869, 1890, 1916, 1977, 2168, 2185, 2384, 2386. It mangles about 11 rows, split at commas inside `⟨…⟩` or `by`. It omits `unfold tt_rsum` (TT:1775), although the brief lists `unfold`. It omits the bare `simp`/`norm_num` calls (TT:1038, 1394, 1918, 1995, 2179, 2228, 2308, 2312). I re-extracted every bracketed argument (560). Every other-file name among the missing ones is a theorem (e.g. `runFrom_zero`, `Cfg.mapState_state`, `step_of_some`, `Action.apply_workTapes`/`_workTapePos`, `zoneTrackTape_empty`, `initCfg_eq`, `Cfg.init_workTapes`, `inputSymbol_of_zero`, `inputSymbolInner`). **There is no rule-10 violation.** The bare simps cannot unfold another file's definition: the closure's only `@[simp]` definitions are `Cfg.init`, `Action.apply` and `initCfg`, all three under `[-simp]`. | Regenerate the table with a bracket-aware extractor. Correct "586 arguments … every argument". |
| F4 | minor | TT:433–481, 514–585 (route step 3; brief :397–398, :662–663) | **ZP-1 is not cited.** The brief says to cite `zoneRowPre_mapState_iff` at phase starts and `zoneRowPre_congr` at redirected ends, "at every phase start and redirect". Instead, each phase starts at `tt_cfg` built at the phase's own state type (`tt_cfg_rowPre`). Each endpoint is converted by `tt_mapState_eq_cfg` through `zoneRowPre_iff` and RN-1's canonical `Cfg.mapState_eq_of_fields`. This is disclosed (REPORT §7). I found no re-derivation of state-independence. | The maintainer rules to accept the deviation and records it, or refactors through `Contract.inPhase` (a `bindState` endpoint with `zoneRowPre_congr`). |
| F5 | minor | TT:548–585 `tt_track_seg` | **`Contract.inPhase` (the binding host's contract form) and `Contract.zero` are never used.** The move branch re-walks the argument of Seam's private `inPhase_traj` (`Build/Contract/Seam.lean:214–247`): live exit from `exit_mem` with `none ∉ X`, guard from `cut`, then `phaseHostTM_run`. Step 3 allows "or through `phaseHostTM_run`", so this is not a freeze breach. `inPhase` was applicable, though: the redirect `tt_red` meets its `hred`/`hsome`, and every target is another phase. The REPORT does not say `inPhase` was bypassed. | Disclose it in REPORT and the integration ledger. Optionally refactor through `inPhase`, with `Contract.zero` for stays, in the dedup window. |
| F6 | minor | `evidence/logs/final/semantic-search.txt`; TT:1296–1315 | **The semantic search is not per private** (brief :651–654). It has 15 family phrase searches with raw hit counts and no dispositions, and `exact?` was posed to 6 statements only (this missed F1). `tt_inputSymbol` repeats the three-case proof of `Cfg.inputSymbol_congr` (CfgFacts:51–61) for an encoded input. Its closer public relative is `SymbolLift`'s `Cfg.liftSymbols_inputSymbol` (`SymbolLift.lean:117`), which is outside the closure and not named in the REPORT. | Add a per-private table. Record `tt_inputSymbol` as a forced re-derivation in the ledger. |
| F7 | minor | evidence | **Claimed but not shipped:** (a) the extended import probe's output ("307 checks, 0 errors"). The extension also counts non-names, e.g. `#check @MultiTapeTM.runFrom_succ_eq_step.trans` at `G5ImportProbeExt.lean:276`, and a duplicate (`workTapePos_runFrom_mem_Icc` at :277 and :321), so "90 further names" overcounts. (b) The `UniversalAxioms.lean` source; only its output is shipped. (c) `Scratch/Probe2`, whose result I reproduced. | Ship the outputs and sources; fix the count. |
| F8 | minor | inbox | **Checkpoint zips cp6 and cp7 are absent.** cp1–cp5, cp8 and the final are present. Checkpoints 6, 7 and 9 landed in one commit (`b8e3a6f0`). cp4, cp5 and cp8 were pushed at 05:16 together with the final, not after each checkpoint. The REPORT lists no zips (checklist item). | State this in the REPORT. |
| F9 | minor | REPORT §8 | **The "departures" sentence is wrong:** "a zone `i` is rebalanced at most once every `2^{i+1}` steps, against the sketch's `2^(i-1)`". `tt_count` (TT:2079, TT:2124–2133) proves a gap of `2^i` for steps of index `> i`. That is: zone `j = i+1` at most once per `2^{j−1}`, exactly the frozen sketch's bound. Separately, the docstring of `tt_count` (TT:2072) says "`2^{i+1}` rounds apart". That is true but stronger than what is formalized. | Drop the sentence ("the construction follows the frozen sketch"). Optionally align the docstring. |
| F10 | minor | TT:2286, TT:724 | **Published facts used that the brief does not name, without escalation or listing** (ground rule 4): `MultiTapeTM.workTapePos_runFrom_mem_Icc`, and the unprimed `runFrom_succ_eq_step` (RO-1 says to use `runFrom_succ_eq_step'`). Both are proved public theorems and harmless. | List them in the REPORT; the maintainer confirms. |
| N1 | note | screens | "Byte-identical to the screen base" is not literally true: the shipped before-screen has an extra trailing `exit 0` line from the wrapper. The content is identical. I re-ran the v3 screen on an export of `71046be0` (7 min, `screen-after-rerun.txt`). It reproduces the shipped after-screen exactly, apart from that line: 1,277 declarations, 843 pairs, 24 new pairs, all `tt_`↔`tt_`, max 89%, no cross-file pair. | — |
| N2 | note | TT:851–969 vs 977–1026 | In-file re-derivation: `tt_full_rebalance_*` re-derive the pre-state that `tt_full_pre_*` package (screen 60%, disclosed). Mirror pairs are at 78–84%. | Cite `tt_full_pre_*` inside `tt_full_rebalance_*`. |
| N3 | note | TT:292, TT:724 | The `Cfg.ext` block in `tt_leaf_step` is against a structure literal, not a renaming, so it is not RN-1 by kind. The RO-1 inline use at TT:724 is disclosed. | Ledger: RO-1 +1 for `TwoTapes`. |
| N4 | note | module docstring (lines 15–47, frozen) | Nothing in it is literally false. Its public claim "No new definitions: the reduction is an existential contract" still holds. At integration it lacks three things: an Implementation section (the REPORT's paragraph, minus F9); Deviations entries for the zone-alphabet machine finished by the alphabet reduction ([AB09, Claim 1.5]) and for `k = 0` by the forwarding embedding; and a size justification (2,464 lines; the policy linter says "must split", the style lint WARN). The frozen target sketch's "`log₂ t + 1` zones" is loose by one against the formal index bound `log₂ T + 1`, which allows up to `log₂ T + 2` levels. | The maintainer updates it at integration. |
| N5 | note | REPORT §2 | It says sorry warnings carry positions, not names. I mapped all 21 positions to declarations at the base: they equal the base list less `two_work_tapes_run`, by name. | — |
| N6 | note | TT:72 | A code comment says "R1 of `M.tm`". This is a registry label that is widely used in library Lean text, and it is not in public text. | Optional. |

## Checks that passed

### 1. Freeze
- **The diff has exactly three hunks:** the import (TT:9), the home insertion after the blank line under `namespace` (TT:51–2417), and the body (TT:2438–2448).
- **Unchanged byte for byte:** the target's statement and docstring, and `two_work_tapes_binary` (statement and proof).
- **No new public declaration.** The 102 privates all carry `tt_`. There is no `section`, `variable` or attribute; the only scoping is `open Classical in` (×3). Region (d) is unused.
- **The patches reproduce `src/TwoTapes.lean`.** The bundle requires only `335d31d4` and has head `71046be0`. `SHA256SUMS` verifies.
- **Every intermediate commit has exactly one `sorry`, in the target's body.**

### 2. Rule 10
- **The sealed copy is the delivered file plus the 46-line seal block** (by diff).
- **The 43 sealed definitions cover:**
  - every other-file TCSlib definition in the walk, except projections and the reducible abbrevs `ZoneSym`, `ZoneCell`, `ZoneData` and `Cfg.Halted`;
  - every other-file definition named anywhere in the source (token intersection).
- **`[-simp]` covers the closure's three `@[simp]` definitions.**
- **The controls are complete and well formed:**
  - 43 rfl, 43 eqn and 3 simp: unsealed 89 PASS / 0 FAIL, sealed 0 PASS / 89 FAIL;
  - the two control files differ only in the seal block, which is identical to the sealed copy's.
- **The data maps are read only through `_eq`, never `_snd`.** `MultiTapeTM.step` is read via `step_of_some`, `Segment` via `segment_iff`, and `Contract.Positive` is unused.

### 3. Route
- **The finish and `k = 0`:** `alphabet_reduction_run` (TT:148); R1 with the `with q₀` equations (TT:71–118).
- **The route-probe lemmas are byte-identical** to `G5Route.lean.txt` (`tt_zero_tapes`, `tt_frame`, `tt_route`).
- **One host, one track step, one leaf:**
  - the host is `phaseHostTM`;
  - `exists_zoneTrackStepTM` is the only track step (no `exists_zoneRebalanceTM`/`ExtendTM`);
  - the leaf `tt_leafTM` is the only own machine, and its docstring carries the required sentence.
- **The iterations use `Segment.iterate_seq`**, for the tracks (TT:648) and for the rounds (TT:1493). All 11 inductions are over tracks, levels or the data orbit; none is over runs of `HS`.
- **The cost uses `sum_cost_le_of_count`** (TT:2394).
- **No hazard is touched:** none of the R3 rows and no private name of another file (rule 11 and my grep).

### 4. Duplication
See N1, F1, F2, F5 and F6.

### 5. Public text
- Every declaration has a docstring.
- Every proof over 20 lines carries `**Proof sketch.**` (29 declarations checked).
- No line exceeds 100 characters (counted in characters).
- There are no campaign labels.

### 6. Sweep and lint
- **The final sweep ran after the final commit**, over the order list exactly (105 modules), all exit 0. It shows 21 sorry warnings, equal to the base less the target. `TwoTapes` shows no warning.
- **Lint:** style lint 0 FAIL / 72 WARN, the new WARN being the size.

## Elaborations used (2 of 3)
1. `rvprobe/g5dreview/G5DSealed.lean`: the delivered sealed copy plus `#print axioms` for the target and `two_work_tapes_binary`. Exit 0, standard axioms (`elab1-sealed.out`).
2. `rvprobe/g5dreview/G5DProbe.lean`: `Option.toList_map` closes `tt_output_map`'s statement. The Mathlib forms of `tt_sum_range_fin` are unknown in the closure, and `exact?` fails on it (`elab2-probe.out`).
