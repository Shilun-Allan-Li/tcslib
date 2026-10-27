**Verdict: issue after edits** (minors and notes only, no blocker, no major). Before issuing, see
decision D1: the review assembled and checked the complete proof of the target, so the fill may not
be needed at all.

# Review: the B5a brief draft (`b5a-fill-unisim.DRAFT.md`, `Turing.MachineFormat.exists_uniformSimulator`)

Read-only review by the maintainer's review sub-agent, 2026-10-27.

**Scope:**
- the draft `campaign/fills/b5a/drafts/b5a-fill-unisim.DRAFT.md`, SHA-256 `6edb5378…8889`,
  rewritten against `Turing.exists_interpreterStartup`;
- its pre-ship `preship-9d0af8cb/` and the junction construction `preship-junction/`;
- the design note's "As built" section, gate 79 (rounds 1 and 2, the round-2 consumer probe);
- background: the earlier B5a review and the wave-1 statement gate's note 34;
- the standards (`policy.md`, `workflow.md`, `TEMPLATE.md`, addendum v2.5).

**Bases:**
- Lean: #169's merged head `9d0af8cb` against `oleans-laplusm`, in the review worktree `wt/`. I
  checked first that the path and `.lake/packages` did not exist, then symlinked the packages.
- The records tip moved from `2c91d57e` to `729ffb99` during the review. The new commits are H's
  pre-ship and megafill D's report; nothing under `campaign/fills/b5a` changed.
- The TCSlib tree is `3fce61e7` at `9d0af8cb`, at #169's merge `94296486` and at the tip. The
  owned blob is `733a9a46`, unchanged (`out/00-bases.txt`).

**Method:**
- Lean ran only through `tools/leanelab.sh`, one file at a time. There was no `lake build`, no cache
  fetch and no copy-text screen run.
- Every file was treated as data. `wt-hk`, the main checkout and `exchange/` are untouched. The
  only write to `wt-hk` was a `git apply --check`, which changes nothing.
- Every claim below cites a file under this folder (`out/`, `probe/`).

## Summary

**The route is sound and sufficient, and the review proved the target end to end.**
- **The proof:** `probe/B5aReviewAssembly.lean` is the overlay with eleven `us_` privates at the
  prescribed home (base 8549, inside `StepBlockClients` with `open StepBlock` in force) and a
  33-line body in place of the `sorry`. The privates are `us_install`, `us_locality`,
  `us_verdict`, `us_table_le`, `us_window_verdict`, `us_ledger`, `us_bank`, `us_junction`,
  `us_tail`, `us_start` and `us_run`.
- **Clean run:** it elaborates with 0 errors and 0 warnings in 20 s at 2.6 GB. The target and
  every new private print within `[propext, Classical.choice, Quot.sound]`
  (`out/B5aReviewAssembly.out`).
- **Sealed run:** the same file elaborates sealed over 28 other-file definitions, the union of the
  pre-ship probes' seals, with `-simp` on `MultiTapeTM.initCfg`, `NDTM.initCfg` and `Cfg.init`
  (`out/B5aReviewAssemblySealed.out`). Its 28 controls all close unsealed, and all fail sealed,
  each at its own goal (`out/B5aReviewSealControl.out`, errors at 139–248).
- **Lint:** 0 FAIL. The added region has no line over 100 characters and no new warning
  (`out/lint-assembly.txt`).
- **Size:** the file goes from 8,666 to 9,201 lines: 12 public, 196 private (+11).

**The drafted parts hold up:**
- The statement and docstring quote is byte-identical to the file.
- Every line number is right: statement 8654, `sorry` 8662, home 8549, `-/` 8653, overlay +2.
- Every recorded probe reproduces.
- The startup's citation at `p = F.k` type-checks exactly as written. The installer contract goes
  through `← serializeK_eq`, and `0 < C.k` comes from `us_install`.
- The all-blank start satisfies the startup's hypothesis by `fun _ _ => rfl`. The state type's
  `Fintype`/`DecidableEq` instances are found without `haveI`.
- The ledger closes for one `d` that depends on `F` only, chosen before `α`, `x` and `t`.

**What needs editing** is stale text from the rewrite, and a few gaps an agent would hit when
copying the probes (F2–F9). `suggested-fix.diff` makes 27 asserted replacements: 20 in the draft,
6 comment lines in the import probe and 1 in the clash probe. It applies cleanly at the records tip
(`git apply --check`).

## Checks

| # | Check | Result | Evidence |
|---|---|---|---|
| 1 | Bases | TCSlib tree `3fce61e7` at `9d0af8cb`, `94296486` and the tip `729ffb99`; blob `733a9a46`; the draft unchanged since `2c91d57e` | `out/00-bases.txt` |
| 2 | Statement, docstring, regions | draft 146–174 = file 8552–8580; `…`; draft 176–185 = file 8653–8662. 8,666 lines, 12 public, 185 private. `section StepBlockClients` 8420, `open StepBlock` 8422, home 8549 (blank, between 8548 and `end StepBlockClients` 8550), appendices 8582–8651, `-/` alone 8653, `sorry` 8662; status text 56–63 | `out/00-bases.txt` |
| 3 | Overlay | exactly one sorry warning, `8656:8`; exit 0 | `out/CodeSimulatorOverlay.out` |
| 4 | Imports | neither import's closure contains `CodeSimulator`; both needed (`Nondeterministic` is not in the startup's closure); the overlay's closure adds 8 modules, containing the earlier six; the 9 modules downstream of `CodeSimulator` all import together with the two: 0 diagnostics | `out/closure.txt`, `out/ImportClashProbe.out` |
| 5 | Import probe | 199 checks of 199 names, 0 errors, 0 warnings; 29 prints (27 standard three, 2 none). Extended by the review assembly's 13 further core and Mathlib names: 212 of 212, 0 errors | `out/B5aUSImportProbe.out`, `out/B5aUSImportProbeExt.out`, `out/assembly-names.txt` |
| 6 | Route probe | 0 diagnostics, 5 prints within the standard three | `out/B5aUSRouteProbe.out` |
| 7 | Junction probe | only `8656:8`'s sorry warning; 6 prints within the standard three; 26 s, 2.6 GB | `out/B5aJunctionProbe.out` |
| 8 | Seal controls | `B5aUSSealControl`: 18 errors, all in the sealed section (103–173); `B5aJunctionSealControl`: 20 errors (107–183); one per control, the unsealed sections clean | `out/B5aUSSealControl.out`, `out/B5aJunctionSealControl.out` |
| 9 | **The full route, at the home** | the target proved: 0 diagnostics, the standard three; sealed over 28 with 28/28 controls | `out/B5aReviewAssembly*.out`, `out/B5aReviewSealControl.out`, `probe/B5aReviewAssembly.lean` 8552–9054, 9159–9196 |
| 10 | Probe statements vs their consumers | `us_window_verdict` is `h1HostedVerdict_accepts` at the window with `d.output = []`, the iff bridged by `us_locality`; `us_run`'s hypotheses are the startup's fields verbatim (`run := rfl`, the passive clause up to beta); its conclusion is `us_verdict`'s hypotheses with the same `S` term. Nothing to strengthen | `probe/B5aReviewAssembly.lean` 9159–9196 |
| 11 | Rule 10 | every `rw`/`simp`/`show`/`exact`/`rfl` step in the assembly reads other files' definitions through published lemmas. The remaining `rfl`s close core reductions (`Option.map`, `if_pos`) or constructor projections; `omega`/`ring` act on `ℕ` atoms only. The sealed run confirms | `out/B5aReviewAssemblySealed.out` |
| 12 | Inherited probes | continuation 7's import probe, the statements probe and note 50: 0 errors at the base | `out/CanonCont7ImportProbe.out`, `out/B5aStatementsProbe.out`, `out/CanonNote50.out` |
| 13 | Lint base | `TuringMachine` 0 FAIL, 68 WARN, 84 files; `Diagonalization` 0 FAIL, 2 WARN, 5 files (as the brief says) | `out/lint-base-*.txt` |
| 14 | Duplication | no published deterministic locality, tape-map builder, threshold-to-loop identity, seam-into-embedding run or relabelled-start lemma on the branch, `origin/main` or `origin/complexity/arora-barak-ch7`; the unmerged branches are listed in `out/branches.txt`. Private relatives exist (F8). Coarse identical-line overlap of the review's block: `NDCodeSimulator` 2 lines, `CodeSimulator` 5 (statement lines), `InterpreterStartup`/`UniversalK`/`ExhaustiveReplay` 0 | `out/dup-search-*.txt`, `out/idiom-grep.txt`, `out/line-overlap.txt` |
| 15 | Population | 57 files, matching the description; contains every module the assembly cites (`Finite`, `Embed`, `Seam`, `Loop`, `CounterLoop`, `VirtualInput`, `StepBlock`, `StepBlockLoop`, `Nondeterministic`, `CodeFormat`, `Encoding`, `Configuration`, `StateRenaming`, `InterpreterStartup`) and the hazards | `preship-9d0af8cb/screen-population.txt` |
| 16 | The diff | 27 asserted replacements; `git apply --check` clean at `729ffb99`; the edited probes elaborate with results identical to the originals | `scripts/apply_fixes.py`, `out/*Edited.out` |

**Commands.** `S` is the scratchpad and `W=$S/review/b5a-brief/wt`. Each file runs alone, as
`bash $S/tools/leanelab.sh $W $S/oleans-laplusm rvprobe/<F>.lean` (wrapper `scripts/run.sh <F>`),
with these results:

| `<F>` | Exit | Result |
|---|---|---|
| `CodeSimulatorOverlay` | 0 | 1 warning |
| `B5aUSImportProbe` | 0 | 199 checks, 29 prints |
| `B5aUSImportProbeExt` | 0 | 212 checks |
| `B5aUSImportProbeEdited` | 0 | identical to `B5aUSImportProbe` |
| `ImportClashProbe` | 0 | |
| `ImportClashProbeEdited` | 0 | |
| `B5aUSRouteProbe` | 0 | 5 prints |
| `B5aJunctionProbe` | 0 | 1 warning, 6 prints |
| `B5aUSSealControl` | 1 | 18 errors |
| `B5aJunctionSealControl` | 1 | 20 errors |
| `B5aReviewAssembly` | 0 | no warning, 12 prints |
| `B5aReviewAssemblySealed` | 0 | no output |
| `B5aReviewSealControl` | 1 | 28 errors |
| `CanonCont7ImportProbe` | 0 | |
| `B5aStatementsProbe` | 0 | its own sorry warning; `sorryAx` through the target, as at the base |
| `CanonNote50` | 0 | |

The assembly is built by `scripts/mkassembly.py`, which asserts every insertion, from
`scripts/head-block.txt`, `scripts/junction-body.txt` (the junction probe's block, renamed) and
`scripts/target-body.txt`. The seal file is `scripts/seal-attrs.txt`, and the controls are built
by `scripts/mkcontrols.py`.

## Findings

| # | Severity | Where | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|
| F1 | note | the route; checkpoints 1–5 | **The route proves the target as written, uniformly** (note 34: `S` and `d` are fixed before `α`, `x`, `t`). The startup's citation at `p = F.k` type-checks verbatim. Its `let` conclusion is destructured by `obtain`, with no `dsimp`. `us_run` takes the startup's fields as they come. The ledger has one closed form: `e = d₀ + 2`, `c = a (L₀ + 4) + A (L₀ + 3) + 3B + 50 L₀ + 110`, `d = c + e`. It is proved by `us_ledger` (45 lines) from the startup's bound, `us_install`'s polynomial, `us_table_le`, `F.serialize_eq`, `serialize_decode_length_le` and `length_bits_le_self`. The edge cases need no separate argument. `t = 0` and `\|x\| < t` are inside `h1HostedVerdict_accepts` and `List.take`; the fallback goes through `F.decode`'s totality; `α = x = []` gives `N ≥ 1`. | `probe/B5aReviewAssembly.lean` (`us_ledger` 8658, body 9159–9196); `out/B5aReviewAssembly*.out` | D1. If the brief issues, the diff adds the closed form to step 4 |
| F2 | minor | lines 12, 85–86, 197, 212, 230 | **Stale probe references after the rewrite.** The 9d0af8cb pre-ship dropped the start probe, and the verdict block is now inside the junction probe file. Yet the inputs list (and the comment) name "the route, start, verdict and junction probes". "Every row … is admission-free (the import probe's eight axiom prints)": the probe has 29 prints. The brief points to `B5aJunctionProbe.append.lean.txt`, but the 9d0af8cb pre-ship ran the full overlaid copy `B5aJunctionProbe.lean.txt`, and the `.append` file's header still says "the brief's six imports". | pre-ship README ("Dropped from `a524c36f`'s set"); `out/B5aUSImportProbe.out` (29 prints); `preship-junction/B5aJunctionProbe.append.lean.txt` 1–4 | Diff: name `B5aJunctionProbe.lean.txt` (both blocks after the target, sealed over 11 and 20), the 29 prints, and the two-file probe set |
| F3 | minor | the import probe (an input); "Cited infrastructure" | **The import probe still presents the startup's phases as citations.** Its header says "every public declaration the route cites must resolve". Its sections then list the header passes, the rewinds and counter copy, the window copy, the layout, "the startup kit's eight lemmas, the phase host's four" and H1's step reader, virtual host and clock. The rewritten route cites none of these; the hosts forbid re-walking the startup's phases. The brief's summary of the probe omits them, so the probe and the brief disagree. | `probe/B5aUSImportProbe.lean` 5–7, 23, 45, 55, 65, 185–186 | Diff: mark those sections "context only" in the probe (comments only; results identical, `out/B5aUSImportProbeEdited.out`); one sentence in "Cited infrastructure" |
| F4 | minor | "Read first"; route steps 1, 3; region (d) | **The probes the brief says to copy lack region (d)'s docstrings.** `b5a_install` (a 22-line proof, so it needs a `**Proof sketch.**`), `b5a_locality`, `b5a_verdict`, and the verdict block's `b5a_locality'` and `b5a_window_verdict` have no docstring. `b5a_run`'s docstring names the probe's `b5a_verdict`. `b5a_locality` and `b5a_locality'` are one lemma, and the copy list in step 3 omits it (`us_window_verdict` needs it). Copied verbatim, the landing would need a docstring follow-up PR, as the canonizer's and the seam layout's did. | `probe/B5aUSRouteProbe.lean` 31, 60, 76; `probe/B5aJunctionProbe.lean` 8680, 8690, 9033 | Diff: say so in "Read first" and step 3. `probe/B5aReviewAssembly.lean` 8552–9054 carries docstrings for all eleven, sketches where needed |
| F5 | minor | route step 1 | **`cost` is never defined, and the installer's states are called `entry`, `exit`**, which clash with the startup's `entry` that step 2 restarts at. | draft 308–312, 322 | Diff: `entryI`, `exitI`, and `cost := fun α => a * ((α.length + 1) ^ d₀ + α.length + max α.length (F.serialize F.fallback).length + 1)` |
| F6 | minor | lines 360–361, 410, 449–454, 550, 553 | **Leftovers of the earlier route.** The H1 harvest gate's "cite the hosted loop and its reading lemma": the route cites neither (they are inside `h1HostedVerdict_accepts`). Rule 10 says "`phaseHostTM`'s table is read through `phaseHostTM_run`", but there is no phase host. The population is described as "the route's new imports (six)" and "the kit's module". The REPORT checklist asks for "the tapes chosen for each phase" and "the ledger, phase by phase". The clash probe's docstring says "the five new imports". | draft lines cited; `probe/ImportClashProbe.lean` 14 | Diff |
| F7 | minor | rule 10's reading list and seal | The list omits definitions the copied proofs read: `MultiTapeTM.initCfg` (`initCfg_eq`, `initCfg_with_q₀`), `StepBlock.tableTape`/`summaryTape`/`outputSummary` (`_eq`, `_nil`), `FinTM.ComputesInTime` (`computesInTime_iff`), the seam and the embedding. It also says `counterLoopCfg` is read "through [its] field equations", but `counterLoopCfg` has none; it is read through `counter_cfg_eq`. "Start from the union of the pre-ship probes' seals" leaves the agent to compute the union: 28 definitions, which the review ran with controls. | `CounterLoop.lean` 737–797; `scripts/seal-attrs.txt`; `out/B5aReviewSealControl.out` | Diff: the readings, and the 28 by name |
| F8 | minor | duplication hazards; promotion candidates | **The block's screen and the hazard list stop short of the files they name.** The junction-block screen (54–64%) was run against `CfgRecord`, `SeamLayout` and `InputRewind` only. It was not run against the hazards the brief names (`NDCodeSimulator`'s core junction, `InterpreterStartup`, `UniversalK`, `ExhaustiveReplay`, `NTimeHierarchy`), nor in-file: `us_window_verdict` restates `h1HostedVerdict_accepts`, a pair to justify. The brief says "copy the probe" and also "at 90% or more stop and escalate", so it should measure what it prescribes. The hazard list also misses the closest private relatives. `UniversalK`'s `uk_init_mapState` ("initial configurations commute with a state map") is the identity `us_start` proves, and `uk_loop_run` (the run after a seam into an embedding) has the shape of `us_tail`/`us_run`. `NTimeHierarchy`'s `un_setup` has an in-body start. `us_start` would be a third private variant, so it is a promotion candidate (`policy.md`, *Construction reuse*). The coarse check makes a ≥90% pair unlikely. | `preship-9d0af8cb/junction-block-screen.txt` (3 files); `UniversalK.lean` 1815–1822, 1849–1866; `NTimeHierarchy.lean` 1410–1430; `out/line-overlap.txt` | Diff: the hazards, `us_start` as a candidate, and an issue-time placeholder ⟨the block screen against the whole population⟩. Run it on the review's block (one screen, no Lean beside it) before issue, or in the PR's screen under D1 (A) |
| F9 | note | step 3; pitfall 1 | "Destructure the conclusion's `let` by `dsimp only`" works, but it is not needed: `obtain` sees through the `let` (gate 79's probe; the review's body). The passive clause arrives as `tapes₀ (ιP i)`, which is `fun _ => none` up to beta, and passes to `us_run` unchanged. Step 4's "close with `ComputesInTime.mono`" is done inside `us_verdict`. | `probe/B5aReviewAssembly.lean` 9183–9187 | Diff |
| F10 | note | the pre-ship | The 9d0af8cb pre-ship dropped the home probes ("the fill's home is unchanged"), and its junction block runs after the target, outside `StepBlockClients`. The earlier review's F8 made the same point about the earlier lemmas. The review's assembly is that home probe: every block elaborates unchanged at the home with `open StepBlock` in force. | `probe/B5aReviewAssembly.lean` | Ship it with the pre-ship as the home evidence |
| F11 | note | pre-ship README | "Sealed over 4 and 20": the verdict block's seal has 11 definitions. The brief does not repeat the error. | `probe/B5aJunctionProbe.lean` 8675–8677 | Records only (README, not in the diff) |
| F12 | note | size, budget | A complete delivery is about 535 lines: 11 privates (~500) and a 33-line body. The final file is 9,201 lines, 12 public and 196 private; the lint WARNs for size, as at the base. Checkpoints 1–5 each map to a copied block, plus `us_ledger` and the body. A partial is unlikely. | `out/lint-assembly.txt` | None |

## Decisions

**D1 (F1): how to finish B5a, now that the complete proof exists and passes the seal.**
- **(A) Land the review's proof as a maintainer PR, with its gate (recommended).** This is the
  #169 precedent ("the proof exists"). `probe/B5aReviewAssembly.lean`, minus its `#print` lines,
  is the PR's `CodeSimulator.lean`. It changes regions (a)–(c) only: the imports, about 500 lines at
  the home and the 33-line body (533 lines added in all).
  - The maintainer adds the target's `**Implementation.**` paragraph, rewrites the status text
    (56–63) and the appendices, and runs the screens: the before run is the screen base, the
    after run is on the PR head and covers F8.
  - The PR also needs the downstream replay of `CodeSimulator`'s 9 dependents (expect 25 sorry
    warnings) and the axiom prints of targets 3–8 and `Complexity.baker_gill_solovay`.
  - `us_locality`, `us_bank` and `us_start` stay private, as promotion candidates for the dedup
    window. Publishing them now would touch other files and widen the replay.
  - This saves a megafill slot and a fill round, and gives a gate over finished code rather than a
    brief.
- (B) Issue the edited brief to Codex, with the assembly staged as an input ("copy it"). The item
  becomes a transcription plus the brief's checks. It costs a slot and a fill gate for no new
  mathematics.
- (C) Issue the edited brief without the assembly. The agent re-derives the 33-line body and the
  45-line ledger the review already has. Not recommended.

Under (B) or (C), apply `suggested-fix.diff`, run the block screen of F8 against the 57 files, and
fill the issue-time placeholders (⟨BASE⟩, ⟨IN-FLIGHT⟩, the banner and budget, the queue, and the
new ⟨block screen⟩ placeholder). Re-check that the tree still equals `3fce61e7` if any Lean lands
first; E-Q's `NTimeDiagonalizer` fill would change the base sorry set.

## What the diff changes (by finding)

`suggested-fix.diff` was generated from `orig/` → `edited/` by `scripts/apply_fixes.py`. Each old
string is asserted to occur exactly once.
- F2: the inputs list and the comment, the 29 prints, and both junction-probe paragraphs.
- F3: the import probe's header and five section comments, and the "Cited infrastructure"
  sentence.
- F4: "Read first" (docstrings, one locality lemma) and step 3's copy list.
- F5: step 1's `entryI`/`exitI` and `cost`.
- F6: the H1 gate line, rule 10's phase-host clause, the population, the REPORT checklist (two
  items), and the clash probe's docstring.
- F7: rule 10's readings and the 28-definition seal.
- F8: the hazards, the promotion candidates and the screen placeholder.
- F1 and F9: step 4's closed form and `us_verdict`'s mono, and the `let` pitfall.

Edited lines stay within 100 columns. The title (139) and the table row (101) are pre-existing.

## Files

- `REVIEW.md` (this file) and `suggested-fix.diff`.
- `out/`:
  - `00-bases.txt` and `01-summary.txt`;
  - every probe's raw output (`*.out`, paths stripped, with the command and exit status on the last
    line) and its `/usr/bin/time -l` record (`*.time`);
  - the closure, the duplicate searches (tree, branches, idioms, line overlap), the lints, and
    `assembly-names.txt`.
- `probe/`: every Lean file run, copies of `wt/rvprobe/`. `B5aReviewAssembly.lean` is the
  complete proof, `B5aReviewAssemblySealed.lean` its sealed copy, and `B5aReviewSealControl.lean`
  the 28 controls.
- `scripts/`: the scripts named above, plus `closure.py`.
- `orig/` and `edited/`: the draft and the two probe files before and after the edits.
- `lintroot/`: the scratch root on which the assembly and the base copy were linted
  (`out/lint-assembly*.txt`).
- `wt/` is the review worktree, detached at `9d0af8cb`. Remove it with
  `git worktree remove --force <path>`.
