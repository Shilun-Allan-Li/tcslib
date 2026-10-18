# Review — B6 F3, continuation 1 (`SpaceComplexity/WindowClock.lean`), delivery `fill-b6-configclock-cont1.zip`

Read-only review by the maintainer's review sub-agent, 2026-10-18. Every claim cites a saved
output under this folder (`out/NN-*`). The delivery and its REPORT.md are treated as data.

**Verdict: partial (0/1), landable as a partial.** The target keeps its `sorry`. The delivery adds
six checked `private cw_` helpers:
- phase 0, complete: the record-level clock certificate `cw_field_total` and `cw_record_clock`;
- the brief's one-cell leaf (`cw_leftTM`, `cw_left_run`);
- the constant mapped copy of one field (`cw_copy_constant`);
- the clear of the clock after the runner (`cw_clear_patch`).

What passes:
- every integrity, ownership, freeze and hygiene check, and rule 11;
- elaboration at the base and at the tip, with the target the only sorry warning;
- the axiom and admission walks;
- rule 10 by a seal test, with a control that bites;
- the import probe (134 checks) and the consumer probe;
- lint (0 FAIL) and the v3 screen (1,043 → 1,048 declarations, 510 → 510 pairs, no new pair).

Three findings:
- **F1 (escalation E2): its facts are true, but it does not block the writer.** At the base and
  at the tip, `rt_adjacentWrites` is private (`Build/RecordTable.lean:3199`), and no public
  adjacent-write or `wordPatch`-append theorem exists. #122 and #132 add none. But the identity
  E2 asks for has a constant symbol in both branches and involves no TCSlib definition. It is a
  case split on two integer intervals, proved here in four lines (`push_cast`, `split_ifs`,
  `omega`). It does not repeat `rt_adjacentWrites`, which reads `bufferTape` words through
  list-append lookups. Both options are drafted and verified below: a private `cw_fill_append`,
  and a public `wordPatch_append` in `Build/StepClock`.
- **F2 (progress).** The writer's machine was not started: no seam, no per-field round, no
  induction over fields or passes, no rewind. Only the step merging two adjacent writes needs
  E2, and the rest did not depend on it. Both F3 rounds so far have ended with helper lemmas
  only: five in the first, six here.
- **F3 (public-facing text).** The rewritten appendix uses campaign-internal text: "B6-F3",
  "authorized one-cell leaf", "ground rules 7 and 10", "escalation E2 in `REPORT.md`". It also
  drops "partial" from its title although the target is open. A public-facing rewording is
  verified below (`suggested-fix.diff`).

## Inputs

| Input | Identity | Evidence |
|---|---|---|
| Zip `exchange/inbox/fill-b6-configclock-cont1.zip` | SHA-256 `b59f674a…cb871`, 11 entries | out/01 |
| Extraction `$S/incoming/b6-configclock-cont1/` | every member byte-equal to the zip; no unsafe entry; CRC OK | out/02 (`scripts/zipcmp.py`) |
| `SHA256SUMS` | 10/10 OK; covers every member except itself | out/03 |
| Brief (dispatch copy) `exchange/archive/fills/b6-fill-configclock-cont1.md` | `2196f09e…fe26`, as in REPORT; equal to the base's `briefs/b6-fill-configclock-cont1.md` after `@ANCESTOR@` → base. The base copy equals the records copy `campaign/fills/b6/briefs/…` | out/08 |
| Addendum v1 `exchange/archive/fills/fill-environment-addendum-v1.md` | `a25474c5…2928`, as in REPORT; equal to the base's `briefs/fill-environment-addendum.md` | out/08 |
| Brief inputs | import probe (60 checks), overlay, population, consumer probe, order list (176 modules) and base sorry list: the base copies equal the tip's `campaign/fills/b6/{inputs,orders,logs}/` copies | out/08 |
| Base `94b986d4db7167ab2a8b20d38d4385f11e60be0e` | TCSlib tree `11fcef24` = `531b98a2`'s (#118) | out/05 |
| Snapshots | `oleans-lbapi4` (base), `oleans-lx2b` (tip) | — |
| Campaign tip | `origin/complexity/arora-barak-ch3-4` = `b175e512` (= `wt-hk`), TCSlib tree `06d30610` = `5fd5dce8`'s. The local branch ref `f46ad19b` is an ancestor | out/36 |

Review worktrees, all detached under this folder, each with the `.lake/packages` link:
- `wt-base`, the base;
- `wt-head`, the head `c887ee89`;
- `wt-tipd`, the tip `b175e512` with the delivered patch applied (uncommitted);
- `wt-e2`, the head plus this review's suggested fix (uncommitted; `suggested-fix.diff`).

The bundle head was fetched into `refs/review/b6-f3-cont1`. Lean ran only through
`tools/leanelab.sh`, one elaboration at a time. Screens ran one at a time under `nice -n 10`,
each only when no other screen ran. No build command was run, and the shim
`evidence/runtime/executable-path.c` (`985924ad…4fba7`, the authorized hash) was neither
compiled nor run. Probe files are in `probe/`, scripts in `scripts/`.

## (a) Integrity and scope

| # | Check | Result | Evidence |
|---|---|---|---|
| 1 | Bundle | `verify` okay. One ref, `refs/heads/fill/b6-configclock-cont1` = `c887ee8988303af928793efba941c753b233114b`, the hash REPORT gives ("Local delivery commit"). Its sole prerequisite is the base | out/04 |
| 2 | Head commit | one commit; sole parent exactly the base; author "OpenAI Codex"; changes only `SpaceComplexity/WindowClock.lean` (+150/−10); tree `a81d53a7` | out/05 |
| 3 | Patch | applied at the base in a temporary index, it reproduces the head tree `a81d53a7`; its hunks equal `git format-patch` of the head | out/06 |
| 4 | Delivered file | byte-equal to the head blob `9baf1502` (SHA-256 `fba3964b…`, as in `SHA256SUMS`); `git diff --check` clean | out/06 |
| 5 | Owned regions | 135 lines inserted at the end of (a) the home (before base line 225); 10 lines of (c) the appendix (base 269–278) replaced by 15. (b), the body, is unchanged. 0 lines outside | out/09 (`scripts/regions.py`) |
| 6 | Reversal | removing the inserted home block and restoring the base appendix gives the base byte for byte | out/13 (`scripts/reverse.py`) |
| 7 | Freeze (`declfreeze.py`) | public 4 → 4, none added or removed; the target changes only in its docstring ("authorized body change"); private 5 → 11, none removed or changed | out/10 |
| 8 | Private statements (`privstmt.py`) | `STATEMENT CHANGED: []`; the five phase-0 helpers unchanged | out/11 |
| 9 | Code lines (`stmtcheck.py`) | all 155 base code lines present, in order | out/12 |
| 10 | Hygiene (150 added lines) | no `sorry`, `admit`, `axiom`, `unfold`, `delta`, `set_option`, `open`, `section`, `variable` or attribute (the one "open" hit is appendix prose). One `decide` closes `some false ≠ some true`. `rfl` appears in `rcases` patterns, `Cfg.ext` field closures and `if_pos rfl`; as the transition-table argument of `step_of_tapeAction_move` at the file's own leaf; and in two closures in `cw_copy_constant`, which the seal (row 22) passes | out/15 |
| 11 | Widths | added lines at most 91 characters; no line of the file over 100 (max 96, pre-existing) | out/15 |
| 12 | Rule 11 | 0 hits for the six R3 rows. The five private-name token hits (`T`, `one`, `sum`, `test`, `trans`) are a local type variable, prose, `List.sum` and `.trans`. No other file's private is reached (row 16). All new privates carry the `cw_` prefix | out/16 (`scripts/rule11.py`), out/19 |
| 13 | Imports | unchanged (the two lines, 6–7) | out/07 |
| 14 | Size | 312 → 452 lines; 4 public / 11 private (lint INFO line) | out/52 |

**New private declarations (6)**, in head line order: `cw_field_total` (227), `cw_record_clock` (243),
`cw_leftTM` (266), `cw_left_run` (272), `cw_copy_constant` (291) and `cw_clear_patch` (317).
Their roles are as REPORT's table states.

## (b) Elaboration and axioms

| # | Check | Result | Evidence |
|---|---|---|---|
| 15 | Base file against `oleans-lbapi4` | exit 0; `280:8` `declaration uses 'sorry'` only | out/17 |
| 16 | Head file against `oleans-lbapi4` | exit 0; `420:8` `declaration uses 'sorry'` (the target) only; no error, no other warning | out/18 |
| 17 | Axioms (a scratch copy with prints, an admission walk and a dependency walk) | target `[propext, sorryAx, Classical.choice, Quot.sound]`. Its only direct `sorryAx` user is itself. All 11 privates are within `[propext, Classical.choice, Quot.sound]`; `cw_leftTM` uses none. The prints are equal line by line, after normalizing the module name, to the worker's `axioms.log` | out/19, out/20 = out/21 (out/22) |
| 18 | External privates and equation lemmas | none reached from any of the 11 privates | out/19 (`EXT` lines) |
| 19 | TCSlib constants reached | 50. Lemmas cited: `cfgRecord_length`, `joinFields_length`, `joinFields_cfgRecord_length`, `recordLength_eq`, `record_pos_lt`, `MultiTapeTM.runFrom_zero`/`runFrom_succ_eq_step'`, `step_of_tapeAction_move`, `moveInputPos_zero`, `copyMapTM_run_ofCfg`, `clearTM_run_ofCfg`, `FinTM.bufferTape_nat`/`_left`, `wordPatch_of_mem`/`_of_not_mem`, `Cfg.ext`. The rest are types, constructors, projections and the definitions in the cited statements. All are public at the base. Six (`Action`, `Cfg.inputSymbol`, `Cfg.workTapeSymbols`, `FinTM.fintypeState`, `MultiTapeTM.step`, `moveInputPos`) are reached only through cited statements and are missing from the worker's list | out/19 (`EXTLIST`), out/23 |
| 20 | Import probe | the brief's 60 checks, the worker's 68 additions (copied from `final-sweep.log`) and the six of row 19: 134 checks, appended to the delivered module. 0 errors; the only warning is the target's | out/24 (`probe/F3C1ImportProbeOnHead.lean`) |
| 21 | Consumer probe | the brief's `F3ConsumerProbe.lean.txt` appended to the delivered module: 0 errors; the only warning is the target's | out/25 |
| 22 | Rule 10, seal test | The whole runner home (base and new helpers) is wrapped in a section. It makes `local irreducible` the 17 other-file semireducible definitions the helpers reach or cite: `Cfg.inputSymbol`, `Cfg.workTapeSymbols`, `FinTM.bufferTape`, `FinTM.configBound`, `MultiTapeTM.runFrom`, `MultiTapeTM.step`, `cfgRecord`, `clearTM`, `copyMapTM`, `joinFields`, `moveInputPos`, `posWidth`, `recordLength`, `tapeAction`, `wordPatch`, `fieldsTape`, `RecordAt` (kinds in out/26). **0 errors**; the target's warning only. Control: an example inside the seal that needs `bufferTape`'s unfolding fails as expected. The base's home also passes | out/27 (`scripts/mkseal.py`; `probe/F3C1Seal*.lean`) |
| 23 | Worker's sweep logs | Bootstrap (at the base, `WindowClock:280`) and final sweep (`WindowClock:420`): each 176/176 in the order list's exact order, 0 errors. Each has 28 sorry warnings in 11 modules, equal per module to `audits/logs/b6-fill-configclock-cont1-base-sorries.txt`, which REPORT copies byte for byte (out/08). The bootstrap was measured at the unchanged base, as the brief requires. Not reproducible here (no build) | out/53 (`scripts/sweep.py`) |

Pre-existing, not this delivery: the frozen bridge `FinTM.configBound_le_two_pow` (line 139)
uses `unfold FinTM.configBound`, another file's definition. It predates rule 10, and the seal
starts after it.

## (c) Progress (against the brief's phases)

| Phase / obligation | State | Notes |
|---|---|---|
| 0: discharge `cw_budget`'s `hL` and `hn` | **complete** | `cw_record_clock` applies `cw_budget` with `recordLength_eq` and `record_pos_lt`, at `c = C + Fintype.card M.State + 8` and `W = c · F`, where `F = ((cfgRecord s d τ).map List.length).sum`. Its conclusion is F2's certification hypothesis for `w = List.replicate W true` verbatim, `C * N * (recordLength … + x.length + 1) ≤ Nat.ofDigits 2 (w.map Bool.toNat)`, for every `N ≤ configBound + 1`. It also gives `W ≤ c · L` |
| 1: the one-cell leaf | **complete** | `cw_leftTM` is exactly the brief's `tapeAction i 0 none .neg _` controller. `cw_left_run` gives the endpoint at one step and the strict cut |
| 1: one field's constant write | **endpoint only** | `cw_copy_constant`: `copyMapTM_run_ofCfg` at `extract := fun _ => ()`, `merge := fun _ _ => e`, as an interval of `some e`. It needs delimiters on the source only, so it appends to an existing clock prefix. Fields are blank-separated (`joinFields` intercalates `[none]`), so each field meets the row's `hw` |
| 1: the writer (per-field round, one pass, `c` passes, rewind, contract) | **open** | no machine composed; not inserted (correct: a partial adds no admission) |
| 2: the clear | **endpoint only** | `cw_clear_patch` takes exactly F2's clock endpoint shape (`wordPatch (d.workTapes j) (d.workTapePos j) w'` on the clock tape) with a blank exterior, and returns the whole tape to blank |
| 2: the composition, exits, ledger | **open** | the time and head inequalities stay conditional (`A`, `D` uninstantiated) |

**On route and reusable?**
- All six helpers are on the brief's Route A and reusable as stated.
- The route is sound at the cell level. After `cw_copy_constant`, the clock head is back at the
  field's start, and the cell past the written run is blank. So `skipTM_run_ofCfg` on the clock
  stops one cell past it, and `cw_left_run` returns onto it. `skipTM_run_ofCfg` on the source
  stops at the next field's first cell, since the separator is blank.
- No other file's definition is unfolded (row 22), and no other file's private is used (row 18).
  No host, seam, loop or tape is added.

**F2 (progress).** The writer was stopped as a whole on E2. E2 is needed only where two adjacent
writes merge into one interval. These did not depend on it:
- the per-field round machine (`copyMapTM` → `skipTM` on the source → `skipTM` on the clock →
  `cw_leftTM`, by `seamCompTM`) and its run lemma;
- the rewind of the source by `skipBackTM`;
- the rewind of the clock;
- the writer's statement.

Rule 4 says to stop on the item and continue with the rest. Together with the first round's five
lemmas, F3 now has eleven helpers and no machine.

**Size:** 312 → 452 lines; 4 public / 11 private.

## (d) Escalations

**E2 — "shared adjacent-write bookkeeping is private".**

| Claim | At the base | At the tip (`b175e512`; open #124, #129–#132) | Evidence |
|---|---|---|---|
| `rt_adjacentWrites` is private in `Build/RecordTable.lean`, line 3199 | **true** | **true** (unchanged, line 3199) | out/60 |
| No public adjacent-write or `wordPatch`-append theorem | **true**: `wordPatch` has only `wordPatch_of_mem`/`_of_not_mem` public; `sc_wordPatch_self`/`_twice`/`_frame` are private | **true**. #122 (merged) adds `FinTM.bufferTape_eq`/`bufferTape_of_neg`, the `clockCfg` field equations and `Cfg.stopped_iff`. #132 adds `pairExtractTM_fst_run(_budget)` and `bufferedSecondCfg_*_cast`. #124, #129–#131 add no such lemma either | out/60, out/39 |
| Proving the constant identity "would duplicate existing shared bookkeeping" | **not supported.** `rt_adjacentWrites` is a different statement. Its values are `FinTM.bufferTape u (q − o)`, `bufferTape v (q − (o + u.length))` and `bufferTape (u ++ v) (q − o)`, and its proof unfolds `bufferTape` and uses `List.getElem?_append_left/right`. The requested identity has `some e` in every branch and needs only an interval case split | the same (both lemmas unchanged) | out/31 (option A below) |

**Verified resolution, option A (private, recommended for the continuation).** Probed in the
delivered module's home: 0 errors, axioms `[propext, Classical.choice, Quot.sound]` (out/31).

```lean
/-- Two adjacent constant fills are one constant fill of their combined width.
**Proof sketch.** Split on the cell: the two intervals partition the combined one, and
outside it both sides read the original tape. -/
private lemma cw_fill_append {Γ : Type} (tape : ℤ → Option Γ) (o : ℤ) (a b : ℕ) (e : Γ) :
    (fun z => if o + (a : ℤ) ≤ z ∧ z < o + a + (b : ℤ) then some e
      else if o ≤ z ∧ z < o + (a : ℤ) then some e else tape z) =
    (fun z => if o ≤ z ∧ z < o + ((a + b : ℕ) : ℤ) then some e else tape z) := by
  funext z
  push_cast
  split_ifs <;> first | rfl | omega
```

**Verified resolution, option B (public API, a maintainer PR).** This is the public form of
`rt_adjacentWrites`: with `wordPatch` unfolded, that lemma is exactly this statement. It would go
in `Build/StepClock.lean`, after `wordPatch_of_not_mem`, and it cites only public cell equations.
- At the base: 0 new diagnostics in the full file (out/32; the unchanged file, out/33).
- At the tip: 0 new diagnostics (out/45, out/46).
- Axioms `[propext, Classical.choice, Quot.sound]`.
- Lint: StepClock goes to 1,186 lines and 8 public declarations; `Build` stays at 0 FAIL, 32 WARN
  (out/56, out/57).

The docstring is public-facing.

```lean
/-- **Adjacent patches join**: patching `u` at `cp` and then `v` at `cp + |u|`, right after it,
is patching `u ++ v` at `cp`.

**Proof sketch.** Split on the cell. Inside `u`'s interval both sides read `u`'s letter, since
`u ++ v` begins with `u`; inside `v`'s interval both read `v`'s letter at the offset past `u`;
outside both intervals both read the original tape. -/
theorem wordPatch_append {Γ : Type*} (ct : ℤ → Option Γ) (cp : ℤ) (u v : List Γ) :
    wordPatch (wordPatch ct cp u) (cp + u.length) v = wordPatch ct cp (u ++ v) := by
  (proof in suggested-fix.diff; 20 lines, public lemmas only)
```

With B, the continuation can state its per-field endpoint as
`wordPatch … (List.replicate a e)`. That is the shape of F2's clock endpoint and of
`cw_clear_patch`'s hypothesis. `RecordTable`'s private `rt_adjacentWrites` could later be
re-pointed to it, in the maintainer's dedup window.

Screen, with A, B and the appendix rewording all applied (`wt-e2`): 1,048 → 1,049
declarations, 510 → 510 pairs, **0 new** (out/35, out/59). `wordPatch_append` is screened and
pairs with nothing, not even `rt_adjacentWrites`. `cw_fill_append`'s body is under the
60-character floor.

**Disposition:** a reuse-policy question, not a mathematical or specification gap. The
continuation needs one of A or B, ruled in its brief. No other escalation. Route B was not used,
correctly.

## (e) Duplication and lint

| # | Check | Result | Evidence |
|---|---|---|---|
| 24 | Screen v3 script | SHA-256 `f4feac91…f878f181`, the same at base, head and tip (`scripts/copy-text-screen-v3.py` there) | out/28 |
| 25 | Before (base, the 21-file population) | `declarations screened: 1043; copy pairs …: 510; reproduced text: 147,693 chars` (exit 0, 639 s). Byte-equal to `audits/logs/b6-fill-configclock-cont1-screen-base.txt` minus its comments, and to the worker's `screen-before.txt` | out/29 |
| 26 | After (head) | `1048; 510; 147,693 chars` (exit 0, 632 s); byte-equal to the worker's `screen-after.txt`. Five of the six new helpers are screened; `cw_leftTM`'s body is under the 60-character floor | out/30 |
| 27 | New pairs (`pairdiff.py`, by name, vs before and vs the repo base log) | **0 new pairs and 0 removed**, against both the before run and the repo base log. "new copies: none" is confirmed | out/58 |
| 28 | Known hazards | No pair involves `rt_adjacentWrites`, `rt_advanceCfg(_append)`, `sc_wordPatch_*`, `rt_copyMachine` or `exists_fieldsCopyTM`, or F2's `wr_*`/`wl_*`. The only WindowClock pair is the pre-existing one with the frozen bridge `FinTM.inWindow_of_spaceUsed_le` (67%) | out/30 |
| 29 | Lint, `SpaceComplexity` (the brief's scope) | base and head `style_lint: 0 FAIL, 81 WARN over 107 files`, equal to REPORT. The only difference is WindowClock's INFO line (452 lines; 4 public / 11 private) | out/51, out/52 |
| 30 | Docstrings and sketches | All six new helpers have docstrings. Four carry a "Proof sketch". `cw_leftTM` is a definition. `cw_left_run` is an eight-line proof, under policy §3's threshold. Cosmetic: a double blank line before the target's docstring (head 358–359) | out/15 |

## (f) Landability on the current tip

- **The owned file is unchanged base → tip.** `WindowClock.lean`'s blob is `60e7889e` at the
  base, at `531b98a2`, at `5fd5dce8` and at the tip `b175e512` (out/36). The patch applies cleanly
  at the tip, and the result has the head blob `9baf1502` (out/41).
- **Upstream changes since the base.** WindowClock's 54 upstream TCSlib modules are the same at
  base and tip (out/37). Nine changed, all by additions only: `ClassNP/NTIME`,
  `Build/Convention`, `Build/CounterLoop`, `Build/StepClock`, `Build/VirtualInput`, `CodeParser`,
  `Encoding`, `Nondeterministic` and `Simulation` (out/38, out/39).
- **Elaboration at the tip** (`wt-tipd`, against `oleans-lx2b`):
  - exit 0, 0 errors, only the `420:8` sorry warning (out/42); the tip's own file has `280:8`
    (out/40);
  - the axiom, admission and dependency probe is identical to the base-snapshot run (out/43,
    out/44);
  - the seal, the 134-check import probe and the consumer probe: 0 errors each (out/43).
- **Replay closure at the tip** (`api/mkdownmulti.py`):
  `TCSlib/Complexity/SpaceComplexity/WindowClock`, then the `TCSlib/Complexity/SpaceComplexity`
  facade, 2 modules (out/47). All 107 facade imports have oleans in `oleans-lx2b` (out/48). The
  facade was not elaborated here. The delivery changes no public declaration.
- **Overlap with the open PRs' closures** (out/49, `scripts/overlap.py`):
  - #124 (SeamLayout), #129 (NTimeHierarchy), #130 (UniversalK) and #131 (CodeSimulator,
    UniversalK): no overlap.
  - **#132** (`Build/Primitives`, `Simulation`): its 313-module closure contains both of this
    landing's modules. There is no textual conflict, and #132 is additive (one docstring line
    changed, out/50). But whichever lands second must replay into a snapshot that has the other.
    If #132 lands first, this PR's replay base is #132's result. If this lands first, #132's replay
    covers WindowClock again.
- **Expected sorry count after landing:** unchanged (28 over the 176-module order list). This
  partial removes none and adds none.
- **Environment (REPORT "Runtime"; summary).** Lean failed to start ("failed to locate
  application") and was run with the addendum's shim, at the authorized hash. The workspace was
  lost to a network interruption and rebuilt from a fresh clone at the same base. The shipped
  logs are fresh recovery runs. Two parallel workers ran the final sweep in isolated output
  trees. Nothing here affects the Lean result, which my elaborations confirm for the owned file.

## (g) Recommendation

**Not yet clear to merge**: the landing PR is still to be opened and replayed. It is clear once
the PR's replay passes and its gate is recorded.

**Land as a partial: yes**, by a maintainer PR, like the first F3 partial (#111). Points for the
PR body:
- **Commit.** Cherry-pick `c887ee8988303af928793efba941c753b233114b` from the verified bundle.
  Its prerequisite is `94b986d4`. It touches only `SpaceComplexity/WindowClock.lean`, which is
  unchanged base → tip.
- **A maintainer commit on top** (recommended): the appendix rewording in `suggested-fix.diff`
  (F3), `WindowClock.lean` hunk 2 only. It is a docstring-only change.
  - `wt-e2`, which carries all three hunks, elaborates with only the target's sorry warning
    (out/54), lints at 0 FAIL (out/55), and screens with 0 new pairs (out/35).
  - Option A (`cw_fill_append`, hunk 1) may ride along if the user rules A now.
  - Leave B (the `StepClock` hunk) to its own API PR.
  - Re-elaborate, re-lint and re-screen whatever subset is committed.
- **What it adds:** six private helpers (phase 0 complete; the leaf; the constant field copy;
  the clock clear); no public declaration and no admission; 312 → 452 lines, 4 public / 11
  private.
- **Review table:**
  - integrity (10/10 sums, bundle, patch);
  - scope (owned regions only; no statement changed);
  - base and tip elaboration (the target's sorry only);
  - axiom and admission walks;
  - the rule-10 seal (17 definitions, control bites);
  - import probe 134/134 and consumer probe;
  - lint 0 FAIL, 81 WARN;
  - v3 screen 1,043 → 1,048 declarations, 510 → 510 pairs, 0 new.
- **Replay:** `SpaceComplexity/WindowClock`, then the `SpaceComplexity` facade, into a copy of
  `oleans-lx2b` (or of #132's result, if #132 lands first). The sorry count is unchanged.

**Integration notes on frozen text** (the maintainer's, at integration; report items):
- The module status (lines 29–31) cites `audits/b6-hosts-statements-findings.md`. That path moved
  to `campaign/gates/13-b6-hosts-statements/findings.md` on 2026-10-18. Under the public-facing
  preference, the path and the gate label should go.
- The Route A sketch (head 383–393) still says `W := c_M · L` and names `Turing.copyTM`,
  `Turing.skipTM` and `Turing.scanTM`. The route now in use is `W = c · F ≤ c · L` field cells, by
  `copyMapTM` with a constant merge, skips and the one-cell move. I agree with the worker here.
- "Main definitions: None" can stay. `cw_leftTM` is private, and the section lists public
  definitions; I disagree with the worker on this item.

**Decisions for the user:**
1. **E2's ruling:** A (a private `cw_fill_append`, four lines, now) or B (a public
   `wordPatch_append` in `Build/StepClock` by a maintainer API PR, which also opens the
   `rt_adjacentWrites` re-point). Both are verified. A unblocks the continuation with no
   upstream PR. B is the reusable form.
2. **Appendix wording:** take F3's public-facing rewording at landing, dropping the "B6-F3" label
   from new text, or keep the label for consistency with `WindowRun`'s landed "Fill appendix
   (B6-F2)".

**Continuation 2 (B6 F3 cont2) should:**
1. **Carry the E2 ruling** (A or B) into the brief, and say plainly that an interval case split
   about `ite` is not "record bookkeeping" under rule 7.
2. **Build the writer in checkpoints**, each of which may land alone:
   - the per-field round: `copyMapTM` → `skipTM` (source) → `skipTM` (clock) → `cw_leftTM`, by
     `seamCompTM`, with its run lemma (write `e^{|f|}` at the clock head, advance it by `|f|`,
     move the source to the next field);
   - one pass over `m` fields, by induction, merging by A or B;
   - `c` passes, and the source's rewind by `skipBackTM` between passes;
   - the clock's rewind;
   - the writer's contract: the brief's stub, or REPORT's restated contract.
3. **Then phase 2:** R1-embed the writer on `{0, clock}`, seam to `exists_windowRunnerTM`, clear by
   `cw_clear_patch`, dispatch the three exits, and instantiate `cw_time_bound`'s `A`/`D` and
   `cw_head_bound`.
4. **Tighten rule 4's wording**, as for G4 cont2: stopping on an item does not stop independent
   items. Ask for at least the per-field round if the merge is still open.
5. **Keep the inputs** (probe, population, order list) at the landing commit, at their
   `campaign/` paths. The base sorry count stays 28, and the screen base becomes this review's
   `out/30-screen-after.txt` (plus the re-screen of any maintainer commit).
