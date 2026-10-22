# Review: C1-WC continuation 1, the bounded input window copier (`Turing.exists_inputWindowCopyTM`), delivery `fill-c1-window-cont1.zip`

Read-only review by the maintainer's review sub-agent, 2026-10-18. Every claim cites a saved
output under `out/`, and every script is under `scripts/`. The delivery, its REPORT.md and its
Appendix C draft are treated as data.

**Verdict.** The delivery is an E-RES environment report. Its executable source is the base plus
the permitted status paragraph, and it is intact. Its Appendix C draft is a complete proof on the
brief's route, but it **does not elaborate verbatim**: 7 errors, and the target then inherits
`sorryAx` through error recovery. With **14 small, mechanical repairs** (R1–R14, 33 lines added
and 25 removed in a 429-line draft) it elaborates with **0 errors and 0 warnings**. This holds at
the base (`oleans-lseam2`), at the campaign tip (`oleans-lc6m`) and on #132's head
(`oleans-l132`). The repairs change no declaration, no route step and no mathematical statement.
The target and its 16 `iw_` privates use only `[propext, Classical.choice, Quot.sound]`. Rule 10
holds under a 16-definition seal, which a control shows bites. The one exception is a `decide` that
evaluates `CounterLoopState`'s derived `DecidableEq`, fixed by L4. **Recommendation: land it as a
maintainer-verified fill (the C1-W / #123 precedent), with the repairs and the landing edits
L1–L6. WC needs no further fill round.**

**Not yet clear to merge:** no landing PR exists yet. It needs a branch on the campaign branch, its
2-module replay (`Build/InputWindow` and the `TuringMachine` facade) and its gate.

## Inputs

| Input | Path | Check |
|---|---|---|
| Delivery zip | `exchange/inbox/fill-c1-window-cont1.zip` | SHA-256 `aec149144cd9…f74894` (out/integrity-checksums.txt) |
| Extracted delivery | `$S/incoming/c1-window-cont1-r3/` | = the zip, entry by entry (29) |
| Brief, dispatch copy | `exchange/outbox/fills/c1-fill-window-cont1.md` | `980f5b5d…` |
| Brief, records copy | `$S/wt-hk/campaign/fills/c1/briefs/c1-fill-window-cont1.md` | `634a448e…`; with its 3 `@ANCESTOR@` set to the base it equals the dispatch copy byte for byte |
| Probe, screen population, order list | `$S/wt-hk/campaign/fills/c1/{inputs,orders,logs}/…window-cont1*` | probe `6b1ad909…`, 57 `#check`s |
| Base | `96d60278e4fde29b986ec1d0e59cd07f768fe28a` (TCSlib content = `dac6b3b0`'s) | worktree `wt-base`, snapshot `oleans-lseam2` |
| Campaign tip | `3638965b` (records HEAD has since moved to `2d4253e6`, Addendum v2.3, with no TCSlib change) | worktree `wt-tip`, snapshot `oleans-lc6m` (out/tip-checks.txt) |
| Bundle head | `e71921d76ab6aad55e0a6b0480bccc3bb17cab89` | fetched into `refs/review/c1-window-cont1-r3` |

The worktrees under this folder are all detached: `wt-base` and `wt-patch` (base), `wt-draft` (the
verbatim draft), `wt-repair` (the repaired draft), `wt-land` (the landing candidate), `wt-tip` (the
tip plus the landing candidate and the facade edit) and `wt-132` (#132's head plus the landing
candidate).

## (a) Integrity

All checks pass (out/integrity-checksums.txt, out/integrity-bundle.txt, out/delivered-vs-base.txt,
out/tip-checks.txt):
- `SHA256SUMS` lists 28 entries, all OK, and covers every other entry of the zip.
- `git bundle verify` succeeds. The bundle has one ref, `refs/heads/fill/c1-window-cont1` =
  `e71921d7…`, and its only prerequisite is exactly the base.
- The bundle holds one commit. Its parent is the base, and its author and committer are
  `Codex <codex@openai.com>`. It changes one file (+5/−1).
- The format-patch equals `git format-patch --full-index` of base..head, apart from the `From`
  line and the signature. Applied to the base, it gives blob `5fd404d7…`. That is the bundle's
  blob and the delivered file's.
- The delivered source differs from the base only by the region (c) paragraph (`diff`: 58c58,62).
  With comments stripped it is identical to the base. It has 88 lines and elaborates at the base
  with exactly the target's sorry warning (out/elab-delivered-base.txt).
- `Build/InputWindow.lean` is blob `5fd86b03…` at the base, `dac6b3b0`, `0bf4f085`, `3638965b` and
  `2d4253e6`. It is unchanged from the base to the tip.

## (b) The draft: extraction and elaboration, verbatim vs repaired

**Extraction** (`scripts/extract_draft.py`; out/draft-extraction.log):
- The Appendix C heading is REPORT line 529. Its one ```` ```lean ```` fence runs over lines
  536–966. The draft has 429 lines, SHA-256 `b873d752…` (`out/draft/draft-verbatim.lean`).
- The draft is a whole file:
  - Its lines 1–37 equal the base's lines 1–37: header, imports, module docstring and
    `namespace Turing`.
  - Its target docstring and statement (lines 308–351) equal the base's lines 38–81.
  - Region (a) is draft lines 38–307 (270 lines, 16 privates). Region (b) is draft lines 352–427
    (76 lines).
- Inserting (a) after base line 37 and (b) in place of base line 82 reproduces the draft byte for
  byte (`out/draft/InputWindow.draft-inserted.lean`, the same hash). There are no other edits.

**Verbatim** (against `oleans-lseam2`; out/elab-draft-verbatim.txt, out/verbatim-errors.txt): exit
1, with 7 errors:

| # | Line:col | Declaration | Error |
|---|---|---|---|
| 1 | 60:74 | `iw_body_copy` (statement) | parse: `unexpected identifier; expected '}'`. A structure-instance field line starts left of the first field's column |
| 2 | 100:8 | `iw_patch_append` | `Unknown identifier Function.update_same` |
| 3 | 105:8 | `iw_patch_append` | `Unknown identifier Function.update_noteq` |
| 4 | 154:2 | `iw_prefix_step` | `apply Cfg.ext rfl`: could not unify `?m = ?m` with the goal |
| 5 | 180:8 | `iw_orbit` | `rw [ih _]`: no `counterLoopOrbit …` after `simp only [roundOrbit_succ]` (the brief's abbrev pitfall) |
| 6 | 241:55 | `iw_local` (statement) | parse: `unexpected token '('`. A `by` block's continuation line starts left of its first tactic |
| 7 | 241:28 | `iw_local` (statement) | unsolved goal `p + n ≤ z.length` (consequence of 6) |

Error 6 makes the parser skip `iw_local`'s body. The target then reports `declaration uses
'sorry'` (329:8), and its body shows 28 linter warnings (14 "does nothing", 14 "never executed").
Errors inside bullets are recovered, so fixing these 7 exposes more: through R5 there are 15
errors (out/stages/elab-through-R5.txt).

**Repairs** (`scripts/repairs.py`, each an asserted single replacement; out/repairs.diff, 33+/25−;
out/repairs-applied.txt):

| Repair | Declaration | Change | Rationale |
|---|---|---|---|
| R1 | `iw_body_copy` statement | first field on its own line | layout only (error 1) |
| R2a–c | `iw_patch_append` | `update_same`→`update_self`, `update_noteq`→`update_of_ne` (×2) | Mathlib renames at the pin, same statements (2, 3) |
| R3 | `iw_prefix_step` | `apply Cfg.ext rfl` → `refine Cfg.ext rfl ?_ ?_ ?_ ?_` | elaborate against the goal first (4) |
| R4 | `iw_orbit` | `rw [ih _]; exact …` → `exact (congrArg (fun x => iw_body.runFrom x 1) (ih _)).trans …` | the abbrev pitfall: `exact` sees through it, `rw` does not (5) |
| R5 | `iw_local` statement | the `by have …; omega` block on its own lines | layout only (6, 7) |
| R6 | `iw_patch_append` | `simp` → `rw [if_pos _, bufferTape_append, add_sub_cancel_left, Function.update_self]` | `simp` cannot rewrite `Function.update`'s dependent argument |
| R7 | `iw_prefix_step` | `rw [← SignType.pos_eq_one, moveInputPos_pos_of_ne_right …]` | the step moves by `(1 : SignType)`; the lemma is stated at `SignType.pos` |
| R8a, b | `iw_local` (both loop calls) | `by decide` → `Nat.one_pos`; `by omega` → `by dsimp only at hu'; omega` | the round time `(fun _ => 1) _` arrives unreduced (free variables for `decide`, an atom for `omega`) |
| R9 | `iw_local` (exhaustion) | `subst n` → `subst hnd` | `subst n` used `hn : n = min …`, not `hnd : n = d` |
| R10 | `iw_local` (`hfinal`) | as R4 | the abbrev pitfall again |
| R11 | `iw_local` (escape endpoint) | a local equation `hpatch` (by `funext` and `counterWord_length`), then `simp only [counter_cfg_eq, hpatch]` | `iw_patch` unfolds only when applied to a cell, and its width is `(counterWord …).length` |
| R12a, b | target (`hstart`, `hend`) | `… <;> exact ⟨rfl, rfl⟩` | `simp` does not evaluate core's `Fin.lastCases` at the numerals `fin_cases` produces |
| R13a–c | target (last clauses) | add the local `y` to two simp sets; `rw [he, ← hv]; rfl` | the statement's `let y`, and the counter width `v.length = w.length` |
| R14 | `iw_local` | `hp` → `_hp` | unused hypothesis (lint) |

**Repaired** (out/elab-repaired-base.txt; out/stages/summary.txt): through R13c, 0 errors and 1
warning (the unused `hp`). Through R14, **0 errors and 0 warnings**, with no sorry warning
(`out/draft/InputWindow.repaired.lean`, `e4228201…`, 437 lines).

What did not change:
- No declaration was added or removed.
- Whitespace-normalized, the only statement text that changed is `iw_local`'s: R5's `;`
  became a newline and R14 renamed a binder (out/privstmt-draft-vs-landing.txt).
- The machine, the body leaf, the join and `C = 6` are the worker's.

## (c) Correctness, route and rules 10/11

**Axioms** (in-module copy; out/axioms-base.out, out/axioms-summary-base.txt; the landing
candidate: out/landing-IWAx.out, out/axioms-landing-prints.txt; the tip: out/tip-IWAx.out):
- The target and the 16 privates print within `[propext, Classical.choice, Quot.sound]`.
  `iw_body` and `iw_patch` use no axiom, and `iw_machine` uses only `Quot.sound`.
- No `sorryAx` occurs, and no constant in the target's closure uses it directly.

**Route** (the landing file, `out/draft/InputWindow.landing.lean`; out/closures.txt):
- **Host.** The machine is `embedEmitTM ι iw_machine` (line 363), with
  `ι = iw_select j dst hjd`, which sends `0 ↦ dst` and `1 ↦ j` (line 312). This is R1's embedding,
  emitting with an empty prefix; the body is silent.
- **Exit join.** `iw_machine` (line 187) is `counterLoopTM iw_body false (some true)`, with
  `.escape ↦ FinTM.controlAction 0 (some .done)` (one stationary, silent step) and every other
  state unchanged.
- **Body leaf.** `iw_body` (line 41) is the brief's one-step leaf, with τ = 1.
- **Agreement.** `iw_join_prefix` uses `MultiTapeTM.runFrom_eq_of_agreeOn` on
  `{q | q ≠ .escape}`, introduced through `MultiTapeTM.agreeOn_iff` (lines 201–202).
- **No forbidden pieces.** There is no `phaseHostTM` (0 occurrences), and no second counter loop,
  embedding or seam.
- **Ledger.** `C = 6`.
  - Exhaustion: `counterOverhead_le` once, T = d + overhead(d + 1) ≤ 6(d + 1) + 2|w|.
  - Early end: `counterOverhead_le_of_le` at r = |y| + 1, T = r + overhead(r) + 1 ≤ 6r + 2|w|.
- **Final counter word.** The final words are `List.replicate |w| true` and
  `counterWord w (|y| + 1)`.
- **First arrival.** The first-arrival clause comes from the loop lemmas' cut clauses, and from
  the `escape ≠ done` state at the join step.

**Statement freeze and scope** (out/declfreeze.txt, out/declnames-landing.txt):
- `declfreeze.py` gives 1 public before and after, and no public declaration added or removed.
  The only body change is the target's (authorized). 16 privates are added, all `iw_`.
- Only two hunks change the code, `37a38,315` and `82c360,435`, exactly regions (a) and (b). The
  landing file adds one maintainer docstring edit (L5).
- Imports are byte-identical to the base's (out/landing.patch, out/hygiene.txt).
- No added `open`, `section`, `variable`, `attribute`, `set_option`, `unfold`, `axiom`, `sorry` or
  `native_decide`.

**Rule 10, seal test** (`scripts/mkseal.py`; out/seal-*.out, out/landing-IWSeal*.out,
out/tip-IWSeal*.out):
- **Seal set.** It is every other-file definition the proof terms reach (out/kinds-defs.txt,
  out/seal-set-S1.txt): `Action.apply`, `Cfg.inputSymbol`, `Cfg.workTapeSymbols`,
  `FinTM.bufferTape`, `FinTM.controlAction`, `MultiTapeTM.AgreeOn`, `MultiTapeTM.runFrom`,
  `MultiTapeTM.step`, `counterLoopCfg`, `counterLoopTM`, `counterOverhead`, `counterWord`,
  `embedEmitCfg`, `embedEmitTM`, `moveInputPos` and `roundOrbit`. All are made
  `local irreducible`. Simp's unfolding of `Action.apply`, the only `@[simp]` definition among them
  (out/simpunfold.out), is erased.
- **S1 (repaired).** 0 errors, 0 warnings.
- **Controls.** Four examples close only by unfolding `runFrom`, `bufferTape`, `counterLoopCfg` and
  `embedEmitCfg`. Under the seal all 4 fail, and nothing else does. Unsealed, all 4 pass.
- **S2.** S1 plus the abbrev `counterLoopOrbit`, forced irreducible. Exactly the 3 places that read
  the orbit through `roundOrbit_zero`/`_succ` fail: `iw_orbit`'s two cases and `hfinal`. This is
  the reading the brief sanctions ("`exact` and `simp only` do").
- **S3.** S1 plus the derived instances `instDecidableEqCounterLoopState` and
  `counterLoopStateFintype`. Only the `decide` for `some .escape ≠ some .done` fails (repaired
  line 308): **F2**. With `simp` in its place (L4) S3 passes, both repaired and landing, at the
  base and at the tip, with the controls biting (4 of 4).

**Rule 10, inspection** (out/rwargs-pass1.txt, out/hygiene.txt):
- **Rewrite and simp arguments.** There are 172 rewrite/simp/unfold argument occurrences, 76
  distinct. TCSlib arguments are published lemmas only (16, plus `roundOrbit_zero` and
  `Action.apply_workTapePos`); the rest are own `iw_` definitions, local hypotheses and lets, and
  Mathlib/core lemmas. There is no `unfold` and no `show`.
- **The one `change`.** It restates `counterOverhead_le` at the local `let d`.
- **The 19 `rfl`s.** Each closes a goal about the file's own definitions (`iw_prefix`, `iw_patch`,
  `iw_machine`'s match) or core's `Fin.lastCases`. The seal confirms none needs a sealed
  definition.

**Rule 11** (out/rule11.txt, out/axioms-base.out):
- **R3 rows.** None of the six R3 rows, or their `_ofCfg` forms, is reached.
- **Other files' privates.** The EXT walk reaches none.
- **Token hits.** The token grep's hits (`S`, `T`, `one`, `trans`) are bound variables, English
  and `.trans`.
- **Cited outside the file.** The citations not in the 57-check probe resolve in an 84-check
  extension, with 0 errors at the base and at the tip (out/cited-not-in-probe.txt,
  out/importprobe-review.out, out/tip-C1WindowImportProbeReview.out). They are the theorems
  `FinTM.bufferTape_eq`, `FinTM.controlAction_apply` and `embedEmitCfg_state`, plus the
  types, definitions and instances in the statements.

**Edge cases** (out/edge-cases.out: four in-module examples applying the proved `iw_local`, with 0
errors and 0 warnings):
- `d = 0` takes the exhaustion branch with no round.
- `p = |z|` gives `n = 0`; with `d ≥ 1` the loop escapes at round 1 through
  `Cfg.inputSymbol_of_end`.
- `|y| < d` gives `n = |z| − p`.
- A padded word `[true, false, false]` has value 1, width 3, and its final width is 3.
- The target needs no case hypothesis: `p ≤ |z|` comes from the input head's `Fin` bound
  (line 369).

**Policy §3** (out/proof-lengths.txt): every proof over 15 lines carries a "Proof sketch":
`iw_local` (62 lines), the target (76, in its docstring), `iw_prefix_step` (18) and
`iw_patch_append` (16).

## (d) Duplication and lint

**v3 screen.** The screen ran one at a time under `nice -n 10`, with the script `f4feac91…`
identical at the base, the landing worktree and the records tree (out/screen-*.txt,
out/screen-compare.txt, out/screen-script-sha.txt):
- **Base:** 248 declarations, 102 pairs, 21,076 characters. This is identical to the campaign's
  screen base and to the worker's `screen-before.txt`.
- **Landing, repaired and verbatim:** 264 declarations, 103 pairs, 21,150 characters each. This
  equals the worker's draft-screen figures.
- **New pairs (`pairdiff.py`):** exactly one, in-file: `iw_body_copy reproduces iw_body_blank:
  74/119 = 62%`. Both specialize `iw_one` at the body's anchor, to its two scanned-symbol branches.
  It is below the 90% copy threshold.
- **Other pairs:** no cross-file pair, and no pair with the hazards (`inputSeekStep_run`,
  `inputCopyTM_run_ofCfg`, `phaseHostTM_run`). New copies: none.

**Lint** (out/lint-wt-*.txt): 0 FAIL and 30 WARN over 38 files at the base, the draft and the
landing candidate. The only difference is the module's INFO line: 438 lines, 1 public and 16
private declarations. No line is over 100 characters; the maximum is 99 (out/linewidths.txt).

## (e) Landability

- **At the tip.** The landing candidate elaborates against `oleans-lc6m` with 0 errors and 0
  warnings (out/elab-landing-tip.txt). So do its axiom prints, the S3 seal and controls, the
  57-check probe and the 84-check probe (out/tip-*.out). `landing.patch` applies to the tip's
  file, which equals the base's (out/applycheck).
- **Replay closure.** The closure is 2 modules: `Build/InputWindow` and the `TuringMachine` facade
  (out/closures.txt, at the base and at the tip). Its 20 upstream modules are unchanged from the
  base to the tip. The brief's 81-module order list is exactly the upstream closure of
  {`InputWindow`, the facade} plus both (out/order-recomputed.txt). So the other 79 modules are
  untouched.
- **Facade edit.** The facade, with L6, elaborates at the tip (out/elab-facade-tip.txt). It uses
  the snapshot's `InputWindow` olean, whose public statement is identical.
- **Open PRs** (out/pr-overlap.txt; the heads are the local refs, equal to GitHub's):
  - **#132** (`91154701`; `Build/Primitives`, `Simulation`): its 314-module closure contains both
    of this landing's modules. The landing candidate elaborates on #132's head against
    `oleans-l132` with 0 errors and 0 warnings (out/elab-landing-132.txt). #132 changes none of
    the cited declarations. Whichever lands second must replay `Build/InputWindow` and the facade
    at the merged state.
  - **#133** (`Build/InputDevice`): overlaps only at the facade, with no textual overlap.
  - **#134** (`SpaceComplexity/WindowClock`): no overlap.
  - **#136** (`lean/c1-exhaustive-fill`, newer than the brief's list): no overlap.

## (f) Environment summary (for the E-RES records)

From the worker's logs, as data (out/env-logs-summary.txt):
- **Initial preflight** (15:23Z, addendum v2.1): `nproc` 9, an overlay filesystem (not tmpfs) and
  `memory.max` 8,589,934,592. In use: anon 114,511,872 + kernel 139,902,976 + shmem 0, a headroom
  of 7.763 GiB. Disk free was 28,038,299,648 B (26.11 GiB), with oom 0: **PASS**.
- **Toolchain.** The official Lean 4.25.0 Linux tarball, `97bee7bd…`. The first `--version` failed
  ("failed to locate application"). The Part 2 shim, `executable-path.c` `985924ad…` (the
  addendum's hash), was then used; the reviewer did not compile or run it. Lean then printed
  commit `cdd38ac5`, the pin. The package pins all pass; the doc-gen packages are absent and
  optional.
- **Cache.** `lake exe cache get` (full) attempted 7,506 files: 5,609 downloaded and 1,897 failed.
  The log has 1,889 lines `CONNECT tunnel failed, response 403`, and the command exited 1.
- **Progress sample.** `memory.current` was at the limit, but anon + kernel left 6.61 GiB of
  headroom, with no OOM. This was rightly not treated as a shortage.
- **Cleanup** (15:58:30Z): the worker removed `.lake/packages` and the compiled Lake
  configuration.
- **Retry preflight.** Disk free was 11,864,387,584 B (11.05 GiB): used rose from 4.00 to
  20.17 GB, +16.17 GB. That is below 12 GiB, so **E-RES** (shortfall 1,020,514,304 B). Memory
  headroom was 7.51 GiB (PASS). The worker did not run the bootstrap, sweep, probe or axiom
  prints.
- **Unmeasured hypothesis.** The logs have no `du`, so nothing measures where the space went. A
  likely candidate is the toolchain (about 4.2 GiB per v2.2) plus the run-owned
  `MATHLIB_CACHE_DIR` holding 5,609 archives, which item 4's cleanup does not remove.
- **Against the current addendum:**
  - Under v2.2/v2.3, the cleaned retry's re-check uses the 8 GiB pre-cache floor, so 11.05 GiB
    would have passed.
  - v2.3's narrowed fetch (about 1,000 files) is the fix recorded for the 403s.
  - Suggestion for the addendum: log `du -sb` of the cache directory, `.lake/packages` and the
    runtime before and after a cleanup.

## (g) Recommendation

**Land the draft as a maintainer-verified fill** (the C1-W, PR #123 precedent):
- **What to land.** Land `out/landing.patch` on `Build/InputWindow.lean` (`663e8da3…`, 438 lines):
  the worker's Appendix C plus R1–R14 and L1–L5. Add `out/facade-edit.diff` (L6).
- **What not to merge.** Do not merge the bundle commit `e71921d7`: its status paragraph says
  the contract is unproved.
- **PR body.** Credit the worker's draft (REPORT Appendix C) and list the reviewer's repairs.
- **Before merge.** The replay is 2 modules, chained from the latest merged snapshot. Then the
  gate.

Landing edits (`scripts/landing.py`; out/landing-edits.diff; all verified at the base and at the
tip):
- **L1 (F3).** `iw_body`'s docstring: drop the scope justification "No catalog row provides …",
  which belongs in REPORT, and describe the step. Proposed: "The one-step copy body on one work
  tape. In state `false`, on an input symbol it writes the symbol, moves the tape head and the
  input head right and stays in `false`; at the input's right end it moves to `true` without
  writing or moving."
- **L2 (F3).** `iw_one`: "One live step of a leaf is its selected action …" becomes "One step from
  a live state applies that state's transition at the scanned symbols."
- **L3a–c (F3).** Drop "public" (the project's API rule, not mathematics) from three docstrings.
  `iw_join_prefix`'s sketch then cites `Turing.MultiTapeTM.runFrom_eq_of_agreeOn`.
- **L4 (F2, rule 10).** `decide` becomes `simp` for `some .escape ≠ some .done`. This closes it by
  constructor disjointness, without evaluating the derived instance.
- **L5.** The module docstring: "(sorried)" becomes "(proved)".
- **L6.** The `TuringMachine` facade, line 169: "Sorried." becomes "Proved.".
- **Optional.**
  - Delete `iw_local`'s unused `_hp` and its argument at the call site (F5).
  - Clean up the existing campaign labels in the module docstring ("user decision 5 of
    2026-10-13; the C1 design note §2.2 step U7 and §3.4 device (i)", "U-1") and in the facade
    line ("C1; user decision 5 of 2026-10-13"). These predate this delivery and belong to the
    deferred docstring cleanup.

Findings:

| # | Severity | Item | Fix |
|---|---|---|---|
| F1 | major as delivered, resolved | the draft does not elaborate verbatim (7 errors, then the target depends on `sorryAx`) | R1–R14 (0 errors, 0 warnings) |
| F2 | minor (rule 10) | `decide` evaluates `CounterLoopState`'s derived `DecidableEq` (S3 seal) | L4, verified sealed |
| F3 | minor (public-facing text) | `iw_body`'s "No catalog row …", `iw_one`'s "leaf", "public" ×3 | L1–L3 |
| F4 | info | the module and facade still say sorried | L5, L6 |
| F5 | info | `iw_local` keeps an unused hypothesis (renamed by R14) | optional deletion |
| F6 | info | the worker's checkable claims hold: 429 lines and 16 `iw_` privates, `C = 6` and its ledger, the draft screen (264/103/21,150, one 62% pair), integrity, rule 11 | none |

**Route notes, in case the user prefers another round instead:** keep the worker's route
unchanged and start from `out/draft/InputWindow.landing.lean`. The pitfalls hit here, which a
future brief's pitfall list could carry, are:
- the structure-instance and `by`-block column rules;
- Mathlib's `update_self` / `update_of_ne`;
- `(1 : SignType)` against `SignType.pos`;
- the unreduced round time `(fun _ => 1) _`;
- `iw_patch`-style definitions unfold only when fully applied;
- `Fin.lastCases` at `fin_cases` numerals;
- the statement's `let y`.
