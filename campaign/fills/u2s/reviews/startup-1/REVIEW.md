# Review: U2-S fill delivery (the `k`-generic startup `Turing.exists_selfStartupTMK`, `TuringMachine/UniversalK.lean`)

Read-only review by the maintainer's review sub-agent, 2026-10-17. Every claim cites a saved
output under this directory (`out/NN-*`). The delivery and its REPORT.md are treated as data.

**Verdict: partial (0/1; phase 1 complete, phase 2 partial), landable as a partial.** The target
keeps its `sorry`. The delivery adds 15 proved `private ss_` helpers:
- a cleaned-canonizer bundle and its `ComputesFunInTime`, with blank tapes and zero heads at a
  length-only bound;
- a suffix-uniform first halt of the prefix canonizer;
- a restarted returning capture, with its exact first return, silence and a space bound;
- the tape-index layout.

What passes:
- integrity, scope, freeze and rule 11;
- elaboration at the base and at the stack top;
- the axiom walk, a 21-definition seal test and lint.

The delivery adds no admission.

Findings:
- **F1 (unreported API gap, rule 10).** Phase 2's normalization needs the published
  `bufferedSecondCfg` field equations at indices of `Fin (bufferedCompTM M₁ M₂).k`. They are
  stated at `Fin (M₁.k + (1 + M₂.k))`, so they apply there only by unfolding `bufferedCompTM`'s
  `k` field.
  - Under the seal `rw` fails; unsealed it succeeds.
  - A draft cast-indexed pair (`rfl` in `Simulation.lean`) works under the seal.
  - REPORT records this as "transport proof … not closed", with "escalations: none". Rule 10
    required an escalation naming the lemma.
- **F2 (PR #124).** The delivery contains **no split leaf**: no transition table, no
  redistribution. There is nothing to promote into a proof of `exists_seamLayoutTM`. Its return
  layout does meet `exists_seamLayoutTM`'s preconditions. Gate 43's major 2 (no common return time
  in that contract) is exactly what U2-S needs before it can cite it. See (d).
- **F3 (cosmetic).** Two helpers of more than 20 lines have no literal "Proof sketch":
  `ss_captureInitial` (34 lines) and `ss_capture_indices` (23).

## Inputs

| Input | Identity | Evidence |
| --- | --- | --- |
| Zip `infra_local/fill-u2s-startup.zip` | SHA-256 `f8d588d6…8ada`, 11 entries | out/01 |
| Extraction `$S/incoming/u2s-startup/` | every member byte-equal to the zip, no unsafe entry, CRC OK | out/02 |
| `SHA256SUMS` | 10/10 OK; covers every member except itself | out/03 |
| Brief (dispatch copy) `fill-dispatches/u2s-fill-startup.md` | `6e579c35…552e`, equal to REPORT's; equal to the base's `briefs/u2s-fill-startup.md` after `@ANCESTOR@` → base | out/04 |
| Addendum v1 | `a25474c5…2928`, equal to the base's copy and to REPORT's | out/04 |
| Base `94b986d4db7167ab2a8b20d38d4385f11e60be0e` | TCSlib tree `11fcef24` = `531b98a2`'s (#118) | out/06 |
| Snapshots | `oleans-lbapi4` (base), `oleans-lx2` (stack top `5333b29b`) | — |

Review worktrees, all detached under this folder, each with the `.lake/packages` link:
- `wt-base`, the base;
- `wt-head`, the head `259a349d`;
- `wt-topd`, `5333b29b` with the patch applied (uncommitted).

The bundle head was fetched into `refs/review/u2s-startup`. Lean ran only through
`tools/leanelab.sh`, one elaboration at a time. No build command was run, and the shim was
neither compiled nor run. Probes are in `probe/`, scripts in `scripts/`; hashes in out/40.

## (a) Integrity and scope

| # | Check | Result | Evidence |
| --- | --- | --- | --- |
| 1 | Bundle | `verify` okay. One ref, `refs/heads/fill/u2s-startup` = `259a349d52203807da2d292d81e2c3a56a807dd5`, the hash REPORT gives. Its sole prerequisite is the base. | out/05 |
| 2 | Head commit | one commit; sole parent exactly the base; author "Codex"; only `UniversalK.lean` (+323/−1) | out/06 |
| 3 | Patch | reproduces the head tree `bb436248` at the base. Its hunks equal `git format-patch` of the head; the only difference is that the delivered patch uses full-length `index` hashes. | out/07, out/08 |
| 4 | Delivered file | byte-equal to the head blob `d99bc09d` (SHA-256 `1b82e583…`, as REPORT states) | out/08 |
| 5 | `git diff --check` | clean | out/09 |
| 6 | Owned regions | 1 removed and 323 added lines: (a) the import before base line 10; (b) 310 lines at the home (blank base line 158); (d) the appendix at the closer, base line 187. 0 outside. Region (c), the body, is unchanged. | out/16 |
| 7 | Reversal | removing the import, the home and the appendix gives the base byte for byte | out/17 |
| 8 | Freeze | public 12 → 12; none added or removed; `exists_selfStartupTMK` changes in its docstring only (authorized). Private 0 → 15, all `ss_`. No statement changed. | out/13, out/14 |
| 9 | Code lines | all 80 base code lines present in order | out/15 |
| 10 | Hygiene (added lines) | no `sorry`, `admit`, `axiom`, `unfold`, `delta`, `set_option`, `open`, `section`, `variable` or attribute. `change` occurs only on the file's own `ss_cleanCanonizer`, `ss_sourceSlot` and `ss_captureTape`. No unrestricted `simp`. | out/18 |
| 11 | Widths | added lines at most 97 characters. The file's two lines over 100 (114, 549) are the base's 113 and 227, shifted. | out/18 |
| 12 | Rule 11 | 0 R3-row hits. The private-name token hits are the spelling collisions REPORT already reviewed: `S` (a binder), `Cfg.mapState_state` (the public equation), `one` (prose), `.trans`. | out/37 |
| 13 | Size | 279 → 601 lines; 12 public / 15 private (lint INFO "601 lines > target 600", not a driver) | out/32 |

**The 15 helpers** (head lines; out/41):

| Line | Declaration | Role |
| --- | --- | --- |
| 161 | `ss_cleanCanonizer` (def) | `cleanTM F.tm F.tm.q₀` restarted at `.init F.tm.q₀`, generic in `F` (the brief's step 1) |
| 167 | `ss_cleanCanonizer_run` | its run is `cleanTM`'s from `Cfg.init` (`initCfg_with_q₀`, `runFrom_with_q₀`) |
| 179 | `ss_cleanCanonizer_halts` | `cleanTM_run` with `s` a `Finset.sup` of visited cards |
| 203 | `ss_lengthBound` | a string time bounded by a function of length |
| 217 | `ss_cleanCanonizer_computes` | `ComputesFunInTime f bound`, with blank tapes and zero heads at the bound |
| 248 | `ss_bufferedHalt_iff` | the composite halts iff its source does (`bufferedSecondCfg_state`) |
| 260 | `ss_prefix_first_halt` | the first halt at `3|α| + 4 + t`, uniformly in the suffix |
| 297 | `ss_cleanCanonizer_first_halt` | the first cleaned halt, with output and clean scratch (`exists_first_halt`) |
| 324 | `ss_captureInitial` | the fresh embedded start is `Cfg.init` |
| 360 | `ss_captureTM` (def) | `embedSilentRetTM` restarted at `inl q₀`: no new host |
| 369 | `ss_capture_run` | the first return at the source's halt; silence through it |
| 400 | `ss_capturedPrefix_run` | `∃ t, ∀ w`: the return at `3|α| + 4 + t`, silence, and space `≤ n·(N + 1)` |
| 432, 442, 446 | `ss_sourceSlot`, `ss_captureTape`, `ss_capture_indices` | the source block after the first `k + 2` tapes, the capture tape last, disjointness |

## (b) Elaboration and axioms

| # | Check | Result | Evidence |
| --- | --- | --- | --- |
| 14 | Base against `oleans-lbapi4` | exit 0; sorry at 188, 233, 271 | out/11 |
| 15 | Head against `oleans-lbapi4` | exit 0; sorry only at `510:8`, `555:8`, `593:8` (U2-S, U2-U, U2-E); no error, no other warning | out/12 |
| 16 | Sorry count | 3 → 3, the same declarations | 14, 15 |
| 17 | Axioms (a scratch copy) | every helper within `[propext, Classical.choice, Quot.sound]`; `ss_captureTM`, `ss_sourceSlot` and `ss_captureTape` have `[propext, Quot.sound]`. The three targets are `[propext, sorryAx, …]`, each its own sole `sorryAx` source. Name by name equal to the worker's `axioms.log`. | out/19 |
| 18 | External privates | one is reached: `_private…UniversalStartup…universalPrefix_start._proof_1`. It is an auxiliary proof inside the **public statements** of `prefixCanon_run` and `prefixCanon_start` (the `⟨2|α| + 3, ⋯⟩` bound). This was checked directly on those constants' types (out/20). It is not a citation by the worker; it is a note for MIG-1 hygiene upstream. No equation lemma of another module is reached. | out/19, out/20 |
| 19 | Import probe | the brief's 100 checks, plus REPORT's 68 extra, plus 33 more public TCSlib constants the helpers reach: 174 checks, 0 errors. The 3 sorry warnings are the overlay's own declarations; the brief's pre-ship log has the same three, so the brief's "0 warnings" is a wording erratum. | out/24 |
| 20 | Rule 10, seal test | 21 other-file definitions made `local irreducible` around the home: `cleanTM`, `Cfg.init`, `Cfg.mapState`, `bufferTape`, `bufferedCompTM`, `bufferedSecondCfg`, `initCfg`, `runFrom`, `spaceUsed`, `visitedByTapeHead`, `embedSilentCfg`, `embedSilentRetTM`, `pairEncode`, `prefixCanonTM`, `serializeK`, `tableBitsK`, `unaryFin`, `universalPrefixTM`, `MultiTapeTM.step`, `ComputesInTime` and `ComputesFunInTime`. This is the worker's 17 plus four. Result: 0 errors, the same three warnings. `Cfg.Halted` is a reducible abbreviation (the gate-review r2 §5 case). | out/22, out/23 |
| 21 | Worker's logs | the final sweep checks the 92 modules in the order list's exact order, all `EXIT 0`, with 35 sorry warnings in 15 modules, equal per module to `audits/logs/u2s-fill-base-sorries.txt`. The bootstrap, run at the base plus the import (UniversalK at 189/234/272), has the same 35. The bootstrap log records diagnostics only, with no per-module markers or exit; the final sweep is the complete record. | out/33 |

## (c) Progress (against the brief's phases)

| Phase | State | Notes |
| --- | --- | --- |
| 1: the cleaned canonizer and `ComputesFunInTime` | **complete** | generic in `F`, so the specialization to `E.canonizer` is one line. It covers a canonizer with no work tapes (`Finset.sup` over `Fin 0`). |
| 2: the captured prefix, with the exact configuration at the return anchor | **partial** | the first return `N(α) = 3|α| + 4 + t(α)` is chosen before `∀ w`; silence through `N` and the space bound are proved. The returned configuration is still `embedSilentCfg … (prefix run at N)`: the tape contents are not normalized (see F1). |
| 3: redistribution and rewind | open | not attempted |
| 4: assembly, `T` and `B` | open | not attempted |

**On route.**
- The proved helpers follow the brief's steps 1–3 exactly: the restarted `cleanTM`, the length
  maximum, suffix independence from `prefixCanon_run`'s formula, and the restarted
  `embedSilentRetTM`.
- No host, leaf, embedding or stage proof is re-proved, and no `UniversalStartup` private is
  copied (see (e)).
- The layout fixes `K = m + 1`: the `m` prefix tapes, then the capture tape, after the first
  `k + 2`. That fits the target's `K + (k + 2)` with no extra scratch tape.

**Caveat for the continuation.**
- `ss_capturedPrefix_run` takes `ι : Fin (prefixCanonTM F').k ↪ Fin n`. Rewriting
  `prefixCanonTM_eq` under `ι` is dependent; this is the "transport" REPORT could not close.
- Restate the phase-2 helpers over `FinTM.bufferedCompTM universalPrefixTM F'` from the start.
  The machine in the target is free, and `ss_prefix_first_halt` already rewrites with
  `prefixCanonTM_eq` first.
- Then use F1's cast-indexed pair to read the buffer and canonizer blocks.

## (d) Escalations

REPORT raises none ("Ground-rule escalations: none"). Two items are nonetheless relevant.

**F1: an API gap in phase 2, unreported.** Normalizing the return needs, at the code buffer's
index and at the cleaned canonizer's block:
`(bufferedSecondCfg universalPrefixTM F' c b p tapes heads).workTapes i`, for
`i : Fin (bufferedCompTM universalPrefixTM F').k`, the index type of the embedding's domain.

- **What is published.** `FinTM.bufferedSecondCfg_workTapes` and `_workTapePos` (the
  `simps`-generated specification API) are stated at `a : Fin (M₁.k + (1 + M₂.k))`.
- **The probe** (`probe/U2SPhase2Transport.lean`), at the delivered file's import context, with
  `bufferedCompTM`, `prefixCanonTM`, `universalPrefixTM`, `bufferedSecondCfg` and `tapeBlocks`
  sealed:
  - **(A)** `rw [FinTM.bufferedSecondCfg_workTapes]` at the composite index: **fails** ("did not
    find an occurrence of the pattern"; out/38).
  - **The control**, without the seal: the same `rw` succeeds, leaving a defeq goal (out/39). So
    the published equation is usable there only by unfolding `bufferedCompTM`.
  - **(C)** A draft pair, `FinTM.bufferedSecondCfg_workTapes_cast` and `_workTapePos_cast`,
    whose right sides read `tapeBlocks … (Fin.cast (bufferedCompTM_k M₁ M₂) i)`. Both are proved
    by `rfl` before the seal, standing in for `Simulation.lean`. Used under the seal they
    rewrite cleanly (out/38: no error at (C)).
- **Disposition.** A two-lemma addition to the specification API in `Simulation.lean`. Together
  with the published `tapeBlocks_left`, `_buffer` and `_right` it gives the buffer tape
  (`bufferTape α`), the cleaned block (blank, heads `0`) and the buffer head (virtual position
  `− 1`) at the return. Rule 10 says to escalate in this case, naming the lemma; REPORT does not.
- **Shared.** C1-UN's setup reads the same composite through `prefixCanon_run`
  (`../c1-universal-fill/REVIEW.md`, F2).

**F2: the relation to PR #124 (`Build/SeamLayout.lean`, `exists_seamLayoutTM`, a sorried
statement; gate 43 FAIL 0/2/1/7).**
- **No split leaf was delivered.** The 15 declarations are a cleanup bundle, first-halt and
  capture contracts and index bookkeeping. None defines a transition table or moves the
  serialization (REPORT: "No leaf was added"). Nothing here can be promoted to prove
  `exists_seamLayoutTM`, so its fill remains wholly open.
- **The interfaces fit.**
  - At U2-S's return the capture tape holds `bufferTape (serializeK M)` with its head at
    `|serializeK M|` (`embedSilentCfg_cap` with an empty prefix). That is inside SeamLayout's
    `0 ≤ pos ≤ |s|`.
  - Tapes `k` and `k + 1` are blank at heads `0` (`ss_capture_indices`, `embedSilentCfg_unselected`).
  - With `src` the capture tape, `tbl = k` and `sm = k + 1`, the contract's endpoint is exactly
    the target's two tape functions. Gate 43's note 6 confirms this.
- **What blocks citing it: gate 43's major 2.** `exists_seamLayoutTM` chooses `T` after the
  configuration, input and frame. U2-S needs `∀ α, ∃ T B, ∀ w` with a unique first exit, so it
  needs a common-return-time clause per source word and head. Until the repaired statement
  publishes one, U2-S cannot replace its phase 3 by the contract alone.
- **Recommendation.** Let the U2-S continuation cite the *repaired* `exists_seamLayoutTM` (one
  proof per argument). That needs:
  - #124 landed with the time-uniformity clause;
  - the continuation re-based after #124 (its current base cannot see it);
  - a rule-10 list amended to include it.

  Otherwise phase 3's leaves would duplicate SeamLayout's planned fill. Gate 43's major 1 (the
  sketch's rewinds do not compose) affects whoever fills SeamLayout, not U2-S's citation.

## (e) Duplication and lint

The v3 screen script's SHA-256 is `f4feac91…f181` at this base, head and top (out/44).

| # | Check | Result | Evidence |
| --- | --- | --- | --- |
| D1 | Before (base, the 10-file population) | `declarations screened: 655; copy pairs …: 514; reproduced text: 151,065 chars`, exit 0, 143 s. Byte-equal to `audits/logs/u2s-fill-screen-base.txt` (comments stripped) and to the worker's `evidence/screen-before.txt`. | out/34, out/43 |
| D2 | After (head) | `668; 514; 151,065 chars`, exit 0, 139 s; byte-equal to the worker's `evidence/screen-after.txt`. The +13 declarations come from the 15 new helpers. The screen does not key every declaration, and which two it skips was not checked. | out/35, out/43 |
| D3 | New pairs (`pairdiff.py`, by name, against the before screen and the repository base) | **0 new, 0 removed; no pair has an `ss_` declaration on either side.** The only UniversalK pairs are the two pre-existing `EffectiveMachineCode.toK` / `EffectiveMachineCode2.toK` pairs (55%, 54%). Nothing pairs with any known hazard: `UniversalStartup`'s capture and its privates, `UniversalInterpreter`'s startup, `cleanTM`'s stage lemmas, the catalog `_run_ofCfg` proofs. REPORT discloses an earlier 78/156 match against `Catalog.lean::f2_loop_live_prefix`, removed before the commit; it is absent at the head. **"new copies: none" is confirmed.** | out/43 |
| D4 | Discipline | one screen at a time under `nice -n 10`, each started only when no other screen ran (`scripts/screens.sh`) | out/34–35 `.status` |
| L1 | Lint `TCSlib/Complexity/TuringMachine` | base and head `0 FAIL, 67 WARN over 79 files`; identical outside UniversalK. UniversalK: the unchanged WARN (two public defs without a lemma) and INFO 279 → 601 lines, 12 / 15. At the top: `0 FAIL, 63 WARN over 80 files`. | out/32 |
| L2 | Docstrings | all 15 helpers have one; 6 carry a literal "Proof sketch". F3: the 34-line `ss_captureInitial` and the 23-line `ss_capture_indices` should get one (policy §3, ~20 lines). The appendix is accurate and says the target remains open. | out/18a, out/41 |

## (f) Landability

- **The owned file is unchanged from base to stack top.** The blob is `7e54aa4b` at the base, at
  `531b98a2`, at `6d18902f`, at the tip `4cb6ceb0` and at `5333b29b` (out/25). The patch applies
  cleanly at `5333b29b`, giving the delivered file.
- **Imports.** The upstream closure (49 modules) is the same at head and top (out/26). Ten
  upstream modules changed, all by addition only (+N/−0): `Convention`, `CounterLoop`,
  `StepBlock`, `VirtualInput`, `CodeFormat`, `CodeParser`, `Encoding`, `NDCodes`,
  `Nondeterministic` and `Simulation` (out/27).
- **At the top** (`wt-topd` against `oleans-lx2`):
  - elaboration: exit 0, the same three warnings (out/28);
  - the axiom, admission and external probe is identical to the base run (out/29);
  - the seal test is clean (out/30);
  - the 174-check probe: 0 errors (out/31).
- **Replay closure:** `TCSlib/Complexity/TuringMachine/UniversalK`, then
  `TCSlib/Complexity/TuringMachine/SelfUniversal`, then the `TCSlib/Complexity/TuringMachine`
  facade (3 modules; out/26), into a copy of `oleans-lx2`. Every import of the two consumers has
  an olean there (out/36). No public statement changes, so `SelfUniversal`'s `k = 1` derivation
  is unaffected. Do not append the root `TCSlib`.
- **Expected sorry count after landing:** unchanged.

## (g) Recommendation

**Not yet clear to merge.** The landing PR, its replay and its gate are still to come.

**Land as a partial: yes**, by a maintainer PR on the stack's top.
- **Commit.** Cherry-pick `259a349d52203807da2d292d81e2c3a56a807dd5` from
  `refs/review/u2s-startup`; its prerequisite is `94b986d4`. It touches only `UniversalK.lean`.
- **Optional maintainer commit:** literal Proof sketches for `ss_captureInitial` and
  `ss_capture_indices` (F3).
- **What it adds:** the cleaned-canonizer bundle and its contracts, the suffix-uniform prefix
  halt, the restarted capture and its contract, and the layout. No public declaration and no
  admission.
- **Replay:** the three modules above.

**Decisions for the user:**
1. **F1's API pair** (`bufferedSecondCfg_workTapes_cast` / `_workTapePos_cast`, `rfl` in
   `Simulation.lean`; verified under the seal in out/38). Shared with C1-UN. Add it before
   either continuation is issued.
2. **Phase 3's route.**
   - **(i)** Cite a repaired `exists_seamLayoutTM` once it carries gate 43's common-return-time
     clause and has landed; re-base the continuation after #124.
   - **(ii)** Have U2-S write its own leaves now, accepting a later dedup against SeamLayout's
     fill.

   This review recommends (i).
3. **Promotion.** The cleaned bundle (`ss_cleanCanonizer`, `_halts`, `_computes`, `_first_halt`)
   is generic in the machine. It is a candidate for C1-UN's route (ii) and for B5a's H1. Promote
   it before a second consumer copies it.

**The U2-S continuation should:**
- restate `ss_capturedPrefix_run` over `bufferedCompTM universalPrefixTM F'`;
- normalize the return through F1's pair and the `tapeBlocks_*` and `embedSilentCfg_*` fields;
- clear the code buffer: `skipTM` from the virtual head, which `cleanTM_run` does not fix (it
  has no input-position clause), then `skipBackTM`, then `clearTM`;
- run phase 3 through the decided route, then `FinTM.timed_rewind`, with the time read off the
  run and kept per `α`;
- assemble with `phaseHostTM` and a fresh exit.

**Environment (brief).** Unmodified Lean failed ("failed to locate application"), so the shim was
used, with a matching hash.
- Disk-backed final checks filled the disk at module 13 (`ClassNP/PolyTime`), and a retry ended
  with status 135.
- Recovery: `lake exe cache lookup` with the official `leantar` into `/dev/shm`. Tar extraction
  needed `--no-same-owner`. A stopped parallel recheck is disclosed and not used as a gate.
- No `lake build`; no dependency or source was changed. This supports the addendum
  suggestions: a disk preflight and memory-backed `TCSLIB_OLEANS`/`TMPDIR`.
