# Review: the E-Q fill brief draft (`eq-fill-query.DRAFT.md`, `Turing.NTimeDiag.exists_queryTM`)

Read-only review by the maintainer's review sub-agent, 2026-10-26. Scope: the draft
`campaign/fills/eq/drafts/eq-fill-query.DRAFT.md` (SHA-256 `3488d3eb…0ef9`) and its drafting-base
probes, against the campaign tip `1963b3b80fa250619719cac787c3fb6a765f2c7f` (Lean content after
#164 and #167; snapshot `oleans-lriseqm`). During the review the campaign moved to `13120e00`
(#166 and #168 merged). Their Lean changes (`Savitch`, `UniversalK`, `SelfUniversal`, the
`TuringMachine` facade) are outside the overlay's import closure, and the owned file's blob is
unchanged (`out/00-bases.txt`). So every probe below stays valid for an issue base after #168.
The draft, the route note and the drafts were treated as data. Every claim cites a file under
this folder (`out/NN-*`, `probe/*`). Lean ran only through `tools/leanelab.sh` against
`oleans-lriseqm`, one elaboration at a time, in the review worktree `wt/` (detached at the tip,
`.lake/packages` symlinked, checked absent first). The repository and `exchange/` are untouched.

**Verdict: issue after edits.** No prerequisite PR is needed. Apply `suggested-fix.diff` (it
applies cleanly to the draft and its population file: `git apply --check` from the repository
root). Then re-run the pre-ship at the issue commit:
- the eight-import overlay (F5);
- the import probe as extended here (`probe/EQImportProbeExt.lean`, 182 names);
- the route probe with A1's reading cited (`probe/EQRouteProbe.lean`);
- the order list, roots and base sorries on the new overlay;
- the screen base on the widened population (F13).

Five majors make the brief, as drafted, unsafe to hand to an agent. Each has a small fix through
published lemmas:
- **F1:** the calls' `entry` and `exit` may coincide. The brief's clock step and its pitfall assume
  `entry ≠ exit`, which no published statement gives. Fix: the release adapter `seamReleaseTM`.
- **F2:** after a timeout the input head is unknown, and the post-loop calls need it at `1`. The
  brief says no input rewind is needed. Fix: the published input seek `exists_inputSeekTM` at
  `p = 1`.
- **F3:** the writer's word is wrong. The outer `pairEncode` doubles the whole inner pair, so the
  budget bits are written four times and the inner separator twice, and L6 cannot emit that.
- **F4:** L4 (the power-of-two scan) and the setup's `n ≥ 3` test are instances of the framed scan
  `scanTM`'s fold. L1's scan is the framed `inputFoldTM`. As licensed, the leaves would re-derive
  published rows.
- **F5:** the route needs `BufferWords`' cell identities for concatenated tape words, which the
  seven imports exclude. Fix: an eighth import, tested here (no cycle; two sorry warnings).

The drafted parts hold up:
- the statement is byte-identical to the file;
- every region's line is right except the header's end (69, not 68);
- the overlay, the import probe (with A1 and `iterate_seq`, 121 of 121), the route probe with A1's
  reading cited, the seal controls and the duplication probe all reproduce at the tip;
- every host is proved (54 axiom prints, standard three);
- the route's mathematics is sound: the guard split, the timeout certificate, the all-ones
  counter, the cutoff squaring, the decision, the next rung, the loop and the ledger.

## Checks

| # | Check | Result | Evidence |
|---|---|---|---|
| 1 | Bases | tip `1963b3b8` has the same Lean content as #167's merge `4c8c2e7e` (empty diff). #164 and #167 are ancestors. Owned blob `3cdc4f33a1650df104c752f2783bf5dc734be3b3`, unchanged since `5fd5dce8`. The new tip `13120e00` changes only files outside the closure. | `out/00-bases.txt` |
| 2 | Target, docstring, regions | statement 270–273 identical to the brief's quote. Docstring 248–269, its ` -/` inline at the end of 269. Home 247 (blank; `acceptLang_mem_NTIME` ends 246). `sorry` 273. E-D 275–361. Module header **14–69** (the draft says 14–68). 361 lines, 22 public, 0 private. The overlay's offset is +7 (target 277). | `out/14-statement-regions.txt` |
| 3 | Overlay at the tip | exactly two sorry warnings, `277:8` and `342:8`, exit 0. Closure: 34 TCSlib modules, no `Diagonalization` module (no cycle). | `out/01-overlay.out`, `out/closure.txt` |
| 4 | Import probe, extended by `Complexity.timeConstructible_iff` and `Turing.Round.iterate_seq` | **121 checks of 121 names**, 0 errors, 0 warnings, exit 0 | `out/02-import-probe.out`, `.raw`, `probe/EQImportProbe.lean` |
| 5 | Route probe, stand-in replaced by the published `Complexity.timeConstructible_iff` | 0 diagnostics, exit 0. All 16 lemmas on standard axioms (the 14 printed, plus 2 prints added for the helpers `qy_ladder_succ_eq` and `qy_two_pow_le_ladder`). The published statement equals the stand-in verbatim. | `out/03-route-probe.out`, `probe/EQRouteProbe.lean` |
| 6 | Seal controls | exactly 7 errors, at sealed lines 48–58 (one per control); the unsealed section closes; same error lines as the drafting run. The seal bites. | `out/04-seal-controls.out` |
| 7 | Semantic-duplication probe | 10 of 10 "could not close", as drafted | `out/05-dup-probe.out` |
| 8 | Route soundness | sound except F1–F3 and F6–F9. The review probe proves, sealed over 12 definitions: the released call's first stop (F1), a timed-out call's silence (F2), the input seek home (F2's fix), the query word (F3), `X` (F6), the cube bound (F9). Its 5 extra controls fail sealed only. | `out/06-review-probe.out`, `out/07-review-seal-controls.out`, `probe/EQReviewProbe.lean` |
| 9 | Hosts proved; statements match roles | 54 hosts and named rows print within `[propext, Classical.choice, Quot.sound]`. Statements read in full: install call (positive cut only), input call, clock, conditional, `iterate_seq`, `expandTM`, copy, write, rewind, release adapter, input seek, scan, fold, emitter. | `out/10-host-axioms.out`, `probe/EQHostAxioms.lean` |
| 10 | Duplication | Searched: the tip, the #169 head, the #168 head (before and after it moved), the #166 head, `origin/main` and `origin/complexity/arora-barak-ch7`, by name and statement. No machine-level unpair, power-of-two, unary-product or doubled-emitter row. But L4 and the `n ≥ 3` test are `scanTM` folds, and L1's scan is `inputFoldTM` (F4). Nearest to L2 and L3 is `BinaryArith` (on `main`, F14). `exact?` finds nothing for L1's statement, the writer's word or the cube bound; it suggests `List.flatMap_assoc` for doubling twice. | `out/08-dup-search.txt`, `out/12-review-dup-probe.out`, `probe/EQReviewDupProbe.lean` |
| 11 | Rule 10 feasibility | Published readings exist for every definition the route reads: `Cfg.ofWords_*`, `stateWord_eq`, `clockCfg_*`, `Cfg.mapState_*`, `embedEmitCfg_*`, `counter_cfg_eq` (F10), `phaseHostTM_q₀`, `initCfg_ofWords` (F11), `pairEncode_eq(_dbl)`, `Cfg.stopped_iff`, `seamReleaseTM_runFrom_pos`. The exceptions are the `BufferWords` import (F5) and `entry ≠ exit` (F1). 182 names, 8-import header: 0 errors. | `out/13-import-probe-ext.raw`, `probe/EQImportProbeExt.lean` |
| 12 | `BufferWords` as an eighth import | closure has no `Diagonalization` module; overlay with 8 imports: two sorry warnings at `278:8`, `343:8`, exit 0 | `out/11-overlay-bufferwords.out`, `probe/NTimeDiagonalizerOverlay8.lean` |
| 13 | Lint base | `0 FAIL, 2 WARN over 5 files`. `NTimeDiagonalizer`: 361 lines, 22 public / 0 private. | `out/09-lint-base.txt` |
| 14 | Copy-text screen | not run. The population changes (F13), so the base is re-measured at issue. | — |
| 15 | Agent-facing quality | self-sufficient once F1–F5 are fixed. Each checkpoint can land alone with no admission (1 as a conditional lemma over a stated `M₁` contract). Gaps are in the checklist, the pitfalls and the population (F11, F13, F15). Size estimate plausible (F19). | below |
| 16 | Public-facing text | the brief imposes the rules correctly ((d), `**Proof sketch.**` over 20 lines). The route probe's own docstrings carry campaign labels and one has none (F12). | `probe/EQRouteProbe.lean` 41, 56, 64 |

**Commands** (from `wt/`, `S` the scratchpad, `W=$S/review/eq-brief/wt`, each alone):
`bash $S/tools/leanelab.sh $W $S/oleans-lriseqm rvprobe/<F>.lean` for `<F>` in:
- `NTimeDiagonalizerOverlay` (exit 0, 2 warnings);
- `EQImportProbe` (exit 0, 121 results, 0 errors);
- `EQRouteProbe` (exit 0, 16 axiom lines, no other output);
- `EQSealControl` (exit 1, exactly 7 errors at 48, 50, 52, 54, 55, 56, 58);
- `EQDupProbe` (exit 1, 10 "could not close");
- `EQReviewProbe` (exit 0, 6 axiom lines);
- `EQReviewSealControl` (exit 1, exactly 5 errors at 42–50);
- `EQHostAxioms` (exit 0, 54 lines);
- `NTimeDiagonalizerOverlay8` (exit 0, 2 warnings);
- `EQReviewDupProbe` (exit 1, 3 "could not close", 1 suggestion);
- `EQImportProbeExt` (exit 0, 182 results).

Lint: `nice -n 10 python3 -I scripts/campaign_style_lint.py TCSlib/Complexity/Diagonalization`.
Raw outputs are in `out/`.

## Findings

| # | Severity | Where | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|
| F1 | **major** | Hosts (`f`'s witness); route step 1; pitfall "The clock's stop states"; rule 10's seal list | `exists_installCallTM` (and `exists_inputCallTM`) quantify `entry` and `exit` separately with only a **positive** cut (`0 < t' < t`), so `entry = exit` is consistent with the statement. The library says so (`Build/Contract/Basic` 43–45, 356–362: "may coincide … split on `entry = exit`"), and `exists_inputCallTM`'s own proof splits (`InputCall.lean` 102–108). The brief runs `C_f` under the clock with stop states `{exit}` and its pitfall claims "`entry ≠ exit` at `u = 0`": with `entry = exit` the clock stops at time `0`, and a seam or the phase host would dispatch the call at time `0`. An agent would hit an unprovable step or escalate. | `rv_release_first_stop` (`probe/EQReviewProbe.lean`, sealed over `seamReleaseTM`, `Cfg.mapState`, `Cfg.ofWords`, `Cfg.Stopped` …): from the install call's published clauses alone, `seamReleaseTM C.tm entry` started at the fresh `Sum.inl ()` first stops at `Sum.inr exit` exactly at the call's exit time, whether or not `entry = exit` (`out/06`, controls `out/07`) | Diff: run every call released at its entry (`seamReleaseTM_runFrom_pos`), the clock's stop state `Sum.inr exit`; or split as `exists_inputCallTM` does. Rewrite the pitfall. Add the adapter to "Read first", rule 10 and the seal list. |
| F2 | **major** | Hosts ("No input rewind is needed"); "After the loop"; edge cases; pitfalls | Every call starts at `Cfg.ofWords`, **input head at `1`** (`Cfg.ofWords_inputPos`). Under R1 the call's input head is the host's (`embedEmitCfg` keeps `inputPos`). After the clock's timeout, the host's input head is the call's at some time `v ≤ d` (the clock's frame clause). No published clause of the call determines it. Yet the stage code's install call and the middle's `exists_inputCallTM` run after the loop, also after a timeout. The brief's "no input rewind is needed" is false, and `inputRewindTM` is outside the imports (rule 6 forbids it) and needs the head at `1` or more. | `out/closure.txt` (no `InputRewind`); `exists_inputSeekTM` (`InputCall.lean` 270–310, in the closure); `rv_seek_home`: at `p = 1` with `[true]` on its tape `0` it brings the head home from anywhere within `C (1 + pos + 2)`, output restored; `rv_call_output_nil`: a timed-out call has output `[]` (`MultiTapeTM.output_prefix`) | Diff: after the loop, the input seek at `p = 1` on two dedicated tapes written at the setup, `O(n)`. State the timed-out call's silence and dirty bank, and that no later phase touches it. Decision D1 has the alternative. |
| F3 | **major** | Writer; L6 | `pairEncode (pairEncode B α) t` doubles the **whole** inner pair: `B` with each bit four times, `[false, false, true, true]`, `α` doubled, `[false, true]`, `t`. The brief's order (budget doubled, `[false, true]`, `α` doubled, `[false, true]`, tail) is a different word, and "this is exactly `query_eq`'s word" is false. L6 ("raw, or each bit doubled") cannot emit `B` quadrupled, so an exact writer would need an unlisted leaf ("any further leaf is an escalation"). | `rv_query_word` (sealed, `pairEncode_eq`, `List.flatMap_append`, doubling twice); the `decide` counterexample at `B = [true]`, `α = t = []` (`probe/EQReviewProbe.lean` 31–34); `exact?` names `List.flatMap_assoc` for doubling twice (`out/12`) | Diff: the correct word with its lemmas; L6 emits each bit `r ∈ {1, 2, 4}` times. |
| F4 | **major** | L1, L4; the setup's `n ≥ 3` test; L6's fixed words; hazards | `policy.md` (*Construction reuse*): "a routine that exists is cited, not re-derived". The framed scan `Turing.scanTM` with `scanFold`/`scanKeep` computes `done (w.foldl δ a₀)` on a tape word at exactly `2|w| + 2`, word intact (`scanTM_run_ofCfg`, `scanTM_contract`, `scanResult_fold`). That is L4 and the `n ≥ 3` test, neither of which the brief assigns to a row. L1's scan is `inputFoldTM` (`inputFoldTM_run_ofCfg`, input head back at `1`). Fixed-word emission is `emitAction` with `FinTM.emit_halts`/`emit_run`. The function-level kit also decides unarity (`computesFunInTime_incFixed`, `incFixed_eq_none_iff_replicate`, `computesFunInTime_ifEq`), the route TMSAT's and Nondeterminism's private deciders take. As licensed, L1 and L4 would be gate-level debt (TEMPLATE failure mode 5). | `Catalog.lean` 12835, 12865, 13147; `Contract/Catalog.lean` 445; `Scan.lean` 535, 645; `Simulation.lean` 114, 142; `TMSAT.lean` 891; `out/10` (all proved) | Diff: L4 is not a leaf; L1 is composed from the rows; L2 and L3 justify themselves against `compareTM_contract` and `walkTM_run_ofCfg`. |
| F5 | **major** | Region (a); rule 6; overlay lines | The route builds tape words by concatenation: `1^a` = the rung + one cell; the counter = `copyMapTM` image + a fixed tail; `X` = expansion + rung + two cells; the unary product's appends. Reading those cells needs `FinTM.bufferTape_append_shift`, `_append_mid` and `_unary` (`TuringMachine/BufferWords`). That module is outside the seven imports' closure. The closure has only `bufferTape_eq` and the one-symbol `bufferTape_append`. So rule 6 forces either a private re-derivation of a published lemma (the semantic-duplication rule forbids it) or an escalation. | `out/closure.txt`; `BufferWords.lean` (imports `Simulation` only); `out/11` (8-import overlay, sorry warnings `278:8`, `343:8`); `out/13` (182 names) | Diff: an eighth import, `TCSlib.Complexity.TuringMachine.BufferWords`. Offsets become +8 (target 278; warnings 278 and 343). Decision D2. |
| F6 | minor | Route step 3 | "`expandTM` with the counter `bits (f a)`, then the rung twice and one cell" gives `f a + 2ℓ + 1`. With `a = ℓ + 1`, `X = f a + a + 1 = f a + ℓ + 2`: one copy of the rung and two cells. (The route note has the same slip.) | `rv_X_cells` and the `decide` example at `ℓ = 2` | Diff. |
| F7 | minor | Setup; route step 1 | The clock leaves "some word of the same width" on all `m = \|bits n\| + \|bits D₀\|` counter cells. `copyMapTM` from `bits n` rewrites only the first `\|bits n\|` of them (`copyMapTM_run_ofCfg`: the interval `[pos, pos + \|w\|)`). So "restore it by `copyMapTM` from `bits n`" leaves the tail arbitrary. The setup also never says how the counter is written. The note's "and a constant tail" was dropped. | `exists_stepClockTMVia` (`wordPatch ct cp (w'.map e)`, `w'.length = w.length`); `Catalog.lean` 1310 | Diff: `copyMapTM` from `bits n`, then `writeAdvTM` of `replicate \|bits D₀\| true`, head back to the start, every round. Name `D₀ = c' (c_f + 2)` (`qy_call_bound`). |
| F8 | minor | L2 | A fast witness can output `bits (f a)` far longer than `bits n`. No published lemma bounds a work-tape word by the call's time, so L2's time must not depend on `\|bits (f a)\|`. As specified it could, and then the stopping round's `O(n)` fails. | `exists_installCallTM` bounds `t` by `\|f arg\|`, not the converse; `out/10` | Diff: L2 within a constant times `\|bits n\| + 1` (lockstep, stopping at the shorter word). |
| F9 | minor | Ledger; L3; L5 | The polylogarithmic terms need a cost form and an arithmetic lemma: L3's and L5's costs are unstated (L5 "any polynomial-time scan", although it is a loop, not a scan). `s · O((L+1)²)` and L5's one-off cost close by `(L + 1)³ ≤ 8 · 2^L` and `2^L ≤ n`. | `rv_cube_le` (sealed; `exact?` finds no published form, `out/12`) | Diff: L3 within `O((u + v + K + 1)²)`, L5 within `O((h + 1)³)` from L3 and the rows, and the cube bound in the ledger. |
| F10 | minor | Rule 10 | "`counterLoopCfg`: through its field equations": it has none. Its published reading is `Turing.counter_cfg_eq` (the layout as a constructor: body bank, then counter) with `counterLoopCfg_body`, as `NTimeHierarchy` (1136–1164) and `RecordTable` (2933–2943) read `expandTM_run_ofCfg`'s start and endpoint. | `CounterLoop.lean` 788, 2019 | Diff. |
| F11 | minor | Pitfalls | "A seam's or phase host's initial state has no equation" is half wrong: `phaseHostTM_q₀` exists, and `initCfg_ofWords` gives a machine's start as the blank seam. Missing pitfalls: `writeAdvTM` returns to its own anchor (state `0`), so a seam or the phase host would dispatch it at time `0` (`Contract/Basic` 38–42: through `ReturnContract.release`); the round times are existential and must be chosen before `Round.iterate_seq`, whose `τ` comes first; `P := fun _ => True` suffices. | `Seam.lean` 854; `Convention.lean` (`initCfg_ofWords`); `Scan.lean` 309–326 | Diff. |
| F12 | minor | Pre-ship; route step 5; rule 11 | (a) The route probe has 16 lemmas (14 axiom-printed), plus `qyDecide` and `QyStep`, not "14 lemmas". (b) Step 5 cites `eq_ladder_succ_eq`, the dossier's name; the probe's is `qy_ladder_succ_eq`. (c) `qy_ladder_succ_eq` has no docstring, and two docstrings name campaign items ("A1's reading", "the dossier's `eqDecide`"). Copied verbatim they break (d)'s rules. (d) `QyStep`/`qyDecide` are not `qy_`-prefixed (rule 11). | `probe/EQRouteProbe.lean` (16 theorems), lines 41, 56, 64 | Diff for all four. |
| F13 | minor | Population | The population omits files the route cites: `Build/Convention`, `Encoding`, `StateRenaming`, `BufferWords`, `ClassP/TimeConstructible`. It also omits the in-tree model of the same construction, `Build/SeamLayout` (eight phases on one phase host over catalog rows and private leaves), and L1's private neighbours, `ClassNP/TMSAT`'s and `ClassNP/Nondeterminism`'s unary deciders. | `out/08`; memory rule "screen populations cover citations" | Diff: 29 files (the population file too). Re-measure the base at issue. |
| F14 | minor | Hazards; in-flight list | The route note's hazard "#135's `ClassP/BinaryArith` … ledger [L2] against `BinaryArith`'s `le` (Q-D6)" was dropped. #135 is not in flight: it **merged into `main`** on 2026-10-26 (`9c5344db`), not into this branch. Its poly-time `le`/`lt` (`AddSub`) and unary `mulU` (`Loops`) are the nearest statements to L2 and L3, and the semantic search must include `origin/main`. | `out/00`, `out/08` | Diff. |
| F15 | note | Pitfalls | The clock's exits are injective families `finish r`/`timeout r` over the body state, so the timeout family (`r` unknown) is routed through the phase host. A reducible `abbrev` (`Cfg.Halted`, `counterLoopOrbit`) cannot be sealed and is read through its body (`policy.md`, 2026-10-26). | `StepClock.lean` 1096–1104; `Configuration.lean` 226 | Diff (in F1's pitfall and the seal list). |
| F16 | note | Comment; base; in-flight list | After #168: the issue base is `13120e00` or later, not "the later of #164's and #167's landings". The base's Lean content is "after #164, #166, #167 and #168". In flight remain only the A+ PR #169 and (on `main`) #135. Stage `drafts/eq-fill-query/` as `inputs/`, with the route probe's stand-in removed. Run the issue pre-ship against #168's replay snapshot (`replay-lu2m`). The comment's placeholder list omits "the in-flight list". | `out/00` | Diff (comment, line 71, line 78). |
| F17 | note | Text | "The statement and its docstring, frozen verbatim (lines 248–273):" is followed by the statement only (as in the model brief, which says "the statements:"). The header ends at 69. Region (d)'s paragraph goes before the inline ` -/` at the end of 269. Four non-title lines over 100 columns (128, 130, 133, 261); the diff rewraps the first three. | `out/14` | Diff for the first two. |
| F18 | note | Lint | The file will pass 1000 lines, and the lint then WARNs for size. Pre-disclose that this is expected (file size alone is not a driver), so the agent does not treat it as a failure. | `out/09` | Diff. |
| F19 | note | Size | 2.4–3.9k lines is plausible. The fixes add little: a release wrap per call, one seek phase, a quadrupling parameter. F4 saves a leaf. The one-round checkpoint (900–1,500) is the least certain; a partial is the expected outcome. Two optional simplifications: the cutoff is not needed for linearity (`X ≤ L` gives `X⁴ ≤ L⁴`), and `(unpair h)` can be updated round by round. | — | None. |

## Decisions

**D1 (F2): how the post-loop calls get the input head at `1` after a timeout.**
- **(A) The input seek after the loop (recommended).** `Turing.exists_inputSeekTM` at `p = 1`,
  on two dedicated tapes (`[true]`, blank) written at the setup. It is published, in the closure,
  `O(n)`, and changes nothing else in the ruled route (`rv_seek_home`).
- (B) Reorder: run `g`'s input call in the setup, and keep `α = stageCode h` current at the anchor
  (recomputed after each passed round, while the input head is at `1`). This is also published-only,
  with a polylogarithmic per-round cost, but it moves two pieces of the ruled route and grows the
  round.

**D2 (F5): the import set.**
- **(A) Add `TCSlib.Complexity.TuringMachine.BufferWords` as the eighth import (recommended).** It
  imports only `Simulation`, creates no cycle, and keeps two sorry warnings (`out/11`). The order
  list gains one module, re-measured at issue. The cover draft `megafill-D.DRAFT.md` then says
  "eight imports" (its "Its first edit: its overlay (seven imports)").
- (B) Keep seven, and let the fill re-derive concatenation cell identities as disclosed private
  copies. Not recommended: it is the semantic duplication the brief forbids, and a gate would
  report it.

Everything else is a maintainer edit within the user's 2026-10-25 rulings: unary arithmetic with
cutoffs, the guard split at the function level, `M₁` one composite, the clocked install call.

## What the diff changes (by finding)

`suggested-fix.diff` makes 47 asserted replacements in the draft and adds 8 lines to
`screen-population.txt` (script: `scripts/apply_fixes.py`; edited copies under `edited/`):
- F1: the release, in the hosts, step 1, "Read first", the pitfall and the seal list.
- F2: the input-head bullet replaces "No input rewind is needed"; the seek in the setup, after the
  loop, in checkpoint 5 and in the edge cases; the call's start pitfall.
- F3: the writer's word and L6.
- F4: L1, L4, the `n ≥ 3` test and the gate-guidance sentence.
- F5: region (a), rule 6, the overlay lines and offsets.
- F6–F14: as in the table.
- F16–F18: the comment, the base line, the in-flight list, the statement intro, the header range
  and the lint line.
- The import probe's count becomes ⟨182⟩ (the review's extension); the cited-infrastructure
  summary follows.
- The REPORT checklist gains the calls' releases, the seek, the base sorry list by name, and the
  edge cases' lemmas.

Not in the diff: the cover draft (D2's "eight imports"; its queue table names the brief
`eq/eq-fill-query.md` but its line 17 names `campaign/fills/eq/briefs/eq-fill-query.md`), and the
drafting-base probe records. `probe/` holds their re-run versions: `EQRouteProbe.lean` (stand-in
removed) and `EQImportProbeExt.lean` (182 names, 8 imports).

## Files

- `REVIEW.md` (this file), `suggested-fix.diff`.
- `out/00`–`out/14`: bases, overlay, import probe, route probe, seal controls, duplication probe,
  review probe and its controls, the duplicate search, lint, host axioms, the 8-import overlay,
  the review's `exact?` sample, the extended import probe, statement and regions; `out/closure.txt`.
- `probe/`: every Lean file run (copies of `wt/rvprobe/`).
- `scripts/`: `closure.py` (import closure), `mkroute.py` (the stand-in replacement, asserted),
  `apply_fixes.py` (the diff's edits, asserted).
- `orig/`, `edited/`: the draft and population before and after the edits.
