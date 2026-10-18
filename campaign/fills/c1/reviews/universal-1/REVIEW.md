# Review: C1-UN fill delivery (the universal NDTM and its corollaries, `Diagonalization/NTimeHierarchy.lean`)

Read-only review by the maintainer's review sub-agent, 2026-10-17. Every claim cites a saved
output under this directory (`out/NN-*`). The delivery and its REPORT.md are treated as data.

**Verdict: partial (3/4), landable as a partial.**

- BF, H′ and S are proved, modulo exactly the cited stubs. Target 1 (the universal NDTM) keeps its
  `sorry`.
- Integrity, scope, freeze, rule 10 (a seal test), rule 11, lint and both elaborations pass.
  Landing it removes 3 sorries: 29 → 26 over the 72-module order list.
- **Escalation UN-1 is genuine at the base.** No public lemma describes the first-component
  extractor's terminal tapes, so the setup's cleanup cannot be proved without unfolding. The
  requested lemma is true. This review drafted it inside `Build/Primitives` and checked it: 0 new
  diagnostics in the full file, clean axioms.
- **Two findings.**
  - **F1 (progress).** Phase 3's conditional derivation could have been delivered and was not.
    This review checked it as a private lemma, re-pointed and sealed.
  - **F2 (risk for the continuation).** The setup reads the prefix canonizer's tapes at indices of
    `Fin (prefixCanonTM F).k`. The published `bufferedSecondCfg` field equations do not apply
    there without unfolding. The same gap was found and probed in the U2-S review
    (`../u2s-startup-fill/REVIEW.md`, (d)).

## Inputs

| Input | Identity | Evidence |
| --- | --- | --- |
| Zip `infra_local/fill-c1-universal.zip` | SHA-256 `a8b4e0e1…cc64`, 11 entries | out/01 |
| Extraction `$S/incoming/c1-universal/` | every member byte-equal to the zip, no unsafe entry, CRC OK | out/02 |
| `SHA256SUMS` | 10/10 OK; covers every member except itself | out/03 |
| Brief (dispatch copy) `fill-dispatches/c1-fill-universal.md` | `12086525…1542`, equal to REPORT's; equal to the base's `briefs/c1-fill-universal.md` after `@ANCESTOR@` → base | out/04 |
| Addendum v1 `fill-dispatches/fill-environment-addendum-v1.md` | `a25474c5…2928`, equal to the base's `briefs/fill-environment-addendum.md` and to REPORT's | out/04 |
| Base `83ec6348b325f060cec2a917b45a4eda6e301d84` | TCSlib tree `d066c4b6` = `6d18902f`'s | out/06 |
| Snapshots | `oleans-lndnf` (base), `oleans-lx2` (stack top `5333b29b`) | — |

Review worktrees, all detached under this folder, each with the `.lake/packages` link:
- `wt-base`, the base;
- `wt-head`, the head `483fb579`;
- `wt-topd`, the stack top `5333b29b` with the delivered patch applied (uncommitted).

The bundle head was fetched into `refs/review/c1-universal`. Lean ran only through
`tools/leanelab.sh`, one elaboration at a time. No build command was run, and the shim
`evidence/runtime/executable-path.c` (`985924ad…`) was neither compiled nor run. Probe files are
in `probe/`, scripts in `scripts/`; their hashes are in out/43.

## (a) Integrity and scope

| # | Check | Result | Evidence |
| --- | --- | --- | --- |
| 1 | Bundle | `verify` okay. One ref, `refs/heads/fill/c1-universal` = `483fb579e8dd1a0c63c066f136ef28602fa74973`, the hash REPORT gives. Its sole prerequisite is the base. | out/05 |
| 2 | Head commit | one commit; sole parent exactly the base; author "OpenAI Codex"; changes only `Diagonalization/NTimeHierarchy.lean` (+69/−7) | out/06 |
| 3 | Patch | applied at the base in a temporary index, it reproduces the head tree `c0aad029`; its hunks equal `git format-patch` of the head | out/07, out/08 |
| 4 | Delivered file | byte-equal to the head blob `365103ca` (SHA-256 `c11e38ce…`) | out/08 |
| 5 | `git diff --check` | clean | out/09 |
| 6 | Owned regions | 7 removed and 69 added lines, all in regions (a), (c) and (d). There are 0 outside. Region (b) is unused: no private declaration was added. | out/16 |
| 7 | Reversal | removing the five imports and the four appendices, and restoring the three `sorry`s, gives the base byte for byte. (`stmtcheck.py` lists 12 "missing" lines, out/15. That is a cascade of its in-order matcher: base line 198's removed `sorry` matches head line 322's. The reversal is the exact check.) | out/17 (`scripts/reverse.py`), out/15 |
| 8 | Freeze (`declfreeze.py`) | 5 public before and after; none added or removed; no `STATEMENT CHANGED`. The tool's "UNAUTHORIZED BODY CHANGE" lines are the four owned bodies or appendices, which the brief authorizes. `ntime_hierarchy` is unchanged. | out/13, out/14 |
| 9 | Imports | exactly the five authorized imports, in the prescribed order, after line 9 | out/10 |
| 10 | Hygiene (added code lines) | no `sorry`, `admit`, `axiom`, `unfold`, `set_option`, `open`, `section` or attribute (the grep's "open" and "private" hits are appendix prose). Two `by decide` discharge `0 < 1`. | out/18 |
| 11 | Widths | added lines at most 82 characters; no line of the file over 100 | out/18 |
| 12 | Rule 11 | 0 R3-row hits; 0 hits among 5,093 other-file private short names | out/42 |
| 13 | Size | 342 → 404 lines; 5 public / 0 private | out/37 |

## (b) Elaboration and axioms

| # | Check | Result | Evidence |
| --- | --- | --- | --- |
| 14 | Base file against `oleans-lndnf` | exit 0; sorry warnings at 162, 190, 299, 313, 338 (the five) | out/11 |
| 15 | Head file against `oleans-lndnf` | exit 0; sorry warnings only at `176:8` (target 1) and `318:8` (`ntime_hierarchy`); no error, no other warning | out/12 |
| 16 | Sorry count, module | 5 → 2. The three removed are BF, H′ and S. | 14, 15 |
| 17 | Axioms (a scratch copy with prints and an admission walk) | all five `[propext, sorryAx, Classical.choice, Quot.sound]`. The direct-`sorryAx` sources are as follows. Target 1: itself. BF: `FinNDTM.exists_exhaustiveDecider` and target 1. H′ and S: `ntime_hierarchy`. This is identical to the worker's `axioms.log`, and is exactly "modulo the cited stubs": once target 1 is proved through the setup, BF's sources become the core, the writer and E. | out/19 |
| 18 | External privates, equation lemmas | none reached from any of the five | out/19 (`EXT`) |
| 19 | TCSlib constants reached | 21. The five lemmas are `ndAcceptsWithin_decider_of_universal`, `NTIME.mono`, `mem_NTIME_iff`, `FinNDTM.decidesInTime_iff` and `timeConstructible_poly`; the rest are definitions, types and projections from the statements. All are public at the base and in the brief's list. | out/19 (`EXTLIST`), out/20 |
| 20 | Import probe | the brief's 53 checks, plus the 9 standard lemmas cited, plus 10 escalation interfaces: 72 checks, 0 errors, 0 warnings | out/22 |
| 21 | Rule 10, seal test | the eight other-file semireducible definitions the bodies reach, made `local irreducible` around BF and around H′/S: `NTIME`, `TimeConstructible`, `CodeNDTM.toFinNDTM`, `FinNDTM.AcceptsWithin`, `FinNDTM.DecidesInTime`, `FinTM.ComputesInTime`, `NDTM.HaltsWithin` and `pairEncode`. 0 errors, the same two sorry warnings. `toNDMachineCode` and `decode` are already `[reducible]` and cannot be sealed. | out/21 (`probe/C1UNSealHead.lean`) |
| 22 | Worker's sweep logs | final sweep: 72/72 in the order list's exact order, 0 errors, 26 sorry warnings in 13 modules. That is the base list (`audits/logs/c1-fill-universal-base-sorries.txt`, 29 in 13) minus the three. The bootstrap gives the same 26 after a failed first attempt (bus error, below). | out/38 |

**Procedure note (minor).** The successful bootstrap ran at the *edited* state. It already shows
26 warnings, with `NTimeHierarchy` at 176/318. The brief says to record the base list first. The
worker copied the base list by name from the repository log instead of measuring it. My base
elaboration (row 14) and the one-file change (row 2) cover the gap.

## (c) Progress

| Target / phase | State | Notes |
| --- | --- | --- |
| Phase 1: BF `exists_ndAcceptsWithin_decider` | **proved** (modulo target 1 and E) | one line, the prescribed citation |
| Phase 1: H′ `ntime_hierarchy_of_pos` | **proved** (modulo `ntime_hierarchy`) | the brief's route: `g n + 1 ≤ 2·g n` from positivity; `NTIME.mono` to `2g`; the constant ×2 through `mem_NTIME_iff` and `decidesInTime_iff`; reverse `NTIME.mono`; rewrite `ntime_hierarchy` |
| Phase 1: S `NTIME_linear_ssubset_square` | **proved** (modulo `ntime_hierarchy`) | `timeConstructible_poly 1 0` and `1 1`, each re-expressed by `funext`/`simp only`; domination at `N = 3A + 4` by `nlinarith [Nat.mul_le_mul_right n hn]`, which covers `A = 0` |
| Phase 2: the setup `P` | open (UN-1) | no declaration; escalated |
| Phase 3: target 1 | open | see F1 |

- **On the route.** The proofs follow the brief and the docstrings. They do not transcribe the
  deterministic `time_hierarchy_of_pos`: it is outside the imports, and the screen shows no pair
  (see (e)).
- **Rule 10.** No definition of another file is unfolded (the seal test, row 21).
- **F1 (progress): phase 3 could have been delivered in conditional form.**
  - Rule 4 asks the worker to stop on the blocked item and continue with the rest. Consumer probe
    1's derivation needs only the setup *hypothesis*, so it does not depend on the blocked setup.
  - The worker chose not to copy it (REPORT line 36). Copied verbatim it would have breached rule
    10 twice:
    - it runs `unfold FinNDTM.AcceptsWithin`;
    - it closes the core's start by defeq of `streamStartCfg`.

    This review re-pointed both: `FinNDTM.acceptsWithin_iff`, and a `Cfg.ext` of the five
    `streamStartCfg_*` field equations.
  - **Result** (`probe/un-phase3.lean.txt`): a `private theorem un_universal_of_setup` placed at
    home (b) of the delivered file. It elaborates with twelve other-file definitions sealed. The
    seal adds `guessRunTM`, `embedSilentTM`, `streamStartCfg`, `NDTM.runWith` and `NDTM.initCfg`
    to row 21's list. 0 errors (out/34).
  - Its admission walk is exactly `[ndWriterTM_run_block, exists_ndInterpreterCore]` (out/35).
    The writer is proved on the stack (#123).
  - With it, target 1 is `exact un_universal_of_setup c <setup>`, and the continuation only has to
    build `P`.

## (d) Escalations

**UN-1: true at the base.** The route runs `prefixCanonTM (FinTM.pairExtractTM true false)` on
`pairEncode (pairEncode (bits t) α) x` and must then clear every scratch tape.

- **What is published.**
  - `prefixCanon_complete` gives state, output and the native input position only.
  - `prefixCanon_run` gives the configuration as `bufferedSecondCfg F (F.runFrom (F.initCfg α') t) b …`
    (out/22). The extractor's own configuration is opaque there: its single work tape, its head
    and its virtual input position. The last fixes the code buffer's head.
  - `pairExtractTM_computes`, `_fst`, `_snd` and `_concat` are `ComputesInTime` /
    `ComputesFunInTime` facts: halting and output only.
- **What is private.** The configuration facts are private in `Build/Primitives.lean`:
  `extractCfg`, `extract_block`, `extract_rewind`, `extract_replay_finish` and `extract_run`
  (base lines 707–987).
- **Why it blocks.** The cleanup rows need the tape contents at the head:
  `clearTM_run_ofCfg` wants a delimited word at the head, and `skipBackTM_run_ofCfg` one behind it.
- **The requested lemma is true and provable at the base.** Draft: `probe/un1-draft.lean.txt`,
  122 lines, for `Build/Primitives.lean` after `pairExtractTM_concat`.
  - `FinTM.pairExtractTM_fst_run a b` is the exact form. The extractor first halts at exactly
    `4·|a| + 5`, live before. Its configuration is
    `⟨none, ⟨2|a| + 3, _⟩, fun _ => bufferTape a, fun _ => |a|, a⟩`.
  - `FinTM.pairExtractTM_fst_run_budget a b` is REPORT's interface, verbatim, as a corollary at
    the budget `5·(|z| + 1)`.
  - Two private helpers support them: `extractCfg_congr` and `extract_scan`, the doubled-prefix
    scan as an induction over `extract_block`.
- **Checks on the draft.**
  - In a truncated copy: 0 errors, 0 warnings. Both theorems print
    `[propext, Classical.choice, Quot.sound]` (out/30; earlier iterations are `30-*-v1..v3`).
  - Installed in the **full** base `Primitives.lean`: the 51 diagnostics, shifted, are identical
    to the base file's own 51; there are none in the inserted region; the axioms are clean
    (out/31, out/32, out/33). The three names are unused at the base, at the stack top and on
    `main`.
- **Why the exact form.** It is the more useful one: `capture_run`, `seamCompTM_run_ofCfg` and
  `embedSilentRetTM_run` all take the halting time *and* liveness before it.
- **A route without new API** (a decision for the user):
  - wrap the extractor with Hydroxyi's `cleanTM`, as U2-S does with its canonizer (U2-S's
    `ss_cleanCanonizer` bundle is generic in the machine);
  - this needs a sixth import, `SpaceComplexity/Machines/Clean`, which is not upstream of
    `NTimeHierarchy` (22 more modules);
  - `cleanTM_run` gives no input-position clause, so the code buffer's head is still only
    "a function of α". It is normalized by `skipTM` then `skipBackTM`; `skipTM_run_ofCfg` accepts
    a head inside the word.
- **F2: a further gap ahead, found in the U2-S review.**
  - `bufferedSecondCfg_workTapes` and `_workTapePos` are stated at indices
    `a : Fin (M₁.k + (1 + M₂.k))`. Every embedding of the prefix canonizer has domain
    `Fin (prefixCanonTM F).k`.
  - With `bufferedCompTM` sealed, `rw` with the published equation fails at such an index.
    Unsealed it succeeds, which means it only works by unfolding the `k` field.
  - A draft cast-indexed pair (`bufferedSecondCfg_workTapes_cast` / `_workTapePos_cast`, `rfl`
    in `Simulation.lean`) works under the seal. Evidence: `../u2s-startup-fill/out/38`, `/39`.
  - C1-UN's setup will read the code buffer through the same equations. The continuation needs
    this pair, or a `Fin.cast` discipline of its own.
- **REPORT's other claims, spot-checked.** All hold:
  - 404 lines, 5 / 0 declarations, no new line over 100 (row 13);
  - the axiom walks (row 17);
  - "no proof unfolds any imported campaign definition" (row 21);
  - the R3 and private-name scans (row 12).

## (e) Duplication and lint

The v3 screen script's SHA-256 is `f4feac91…f181` at base, head and top (out/36).

| # | Check | Result | Evidence |
| --- | --- | --- | --- |
| D1 | Before (base, the 6-file population) | `declarations screened: 67; copy pairs …: 14; reproduced text: 3,174 chars`, exit 0. Byte-equal to `audits/logs/c1-fill-universal-screen-base.txt` (comments stripped) and to the worker's `screen-before.txt`. | out/39, out/45 |
| D2 | After (head) | `70; 14; 3,174 chars`, exit 0; byte-equal to the worker's `screen-after.txt`. The +3 declarations are the three filled bodies, now screened. | out/40, out/45 |
| D3 | New pairs (`pairdiff.py`, by name, against the before screen and the repository base) | **0 new, 0 removed**. No pair has an owned-file declaration on either side, so there is no cross-file or in-file pair. Neither known hazard (`time_hierarchy_of_pos` in `TimeHierarchy/Diagonal`, `UniversalStartup`'s cleanup) pairs with the file. **"new copies: none" is confirmed.** | out/45 |
| D4 | Discipline | this review's screens (and the U2-S review's two) ran one at a time under `nice -n 10`, each started only when `pgrep -f copy-text-screen-v3` found none (`scripts/screens.sh`) | out/39–40 `.status` |
| L1 | Lint `TCSlib/Complexity/Diagonalization` | base and head `0 FAIL, 1 WARN over 4 files`, the unchanged EXPCOM WARN; NTimeHierarchy INFO 342 → 404 lines, 5 public / 0 private. At the top: `0 FAIL, 1 WARN over 5 files`. | out/37 |
| L2 | Docstrings | every proved body keeps its literal Proof sketch, and every open declaration keeps its Proof sketch. The appendices are accurate. Two need rewording at landing: target 1's points to `REPORT.md`, an out-of-tree file, and BF's says "in this partial delivery". | out/10 |

## (f) Landability

- **The owned file is unchanged from base to stack top.** Its blob is `cbb0cef8` at the base, at
  `6d18902f`, at the campaign tip `4cb6ceb0` and at `5333b29b`; no commit touches it (out/23).
  The patch applies cleanly at `5333b29b`, giving the delivered file byte for byte.
- **Imports.** The upstream closure (53 modules) is the same at head and top (out/24). Nine
  upstream modules changed (out/25):
  - seven by addition only;
  - `NDHost` (+150/−12) and `NDCodeSimulator` (+3/−3), whose removed lines are docstrings and
    the writer's `sorry` (#123 proves it).

  No declaration the delivery cites changed.
- **Elaboration at the top** (`wt-topd` against `oleans-lx2`): exit 0, only `176:8` and `318:8`
  (out/26).
  - The axiom, admission and dependency probe is identical to the base-snapshot run (out/27).
  - The seal test and the 72-check import probe are clean (out/28, out/29).
- **Replay closure at the top:** `TCSlib/Complexity/Diagonalization/NTimeHierarchy`, then the
  `TCSlib/Complexity/Diagonalization` facade (2 modules; out/24). Since #126 the facade imports
  `NTimeHierarchy`. All six of its imports have oleans in `oleans-lx2` (out/41). Do not append
  the root `TCSlib`.
- **Expected sorry count after landing:** −3 relative to the stack (the three corollaries). At
  the stack top the module's count goes 5 → 2.

## (g) Recommendation

**Not yet clear to merge.** The landing PR is still to be opened, replayed and gated.

**Land as a partial: yes**, by a maintainer PR on the stack's top.
- **Commit.** Cherry-pick `483fb579e8dd1a0c63c066f136ef28602fa74973` from
  `refs/review/c1-universal`; its prerequisite is `83ec6348`. It touches only the owned file.
- **A maintainer commit on top:**
  1. Reword target 1's appendix. Name UN-1 and point to this review's archived path, not to
     `REPORT.md`. Reword BF's "in this partial delivery".
  2. Update the module's status text and "Main results (all sorried…)": three are now proved,
     modulo `ntime_hierarchy` and E.
  3. Optionally, add F1's verified `un_universal_of_setup` at home (b), credited to consumer
     probe 1. That makes target 1 one line once the setup exists. Its re-elaboration and screen
     would then be the review's.

  Then re-elaborate (expect `176:8` and `318:8` only), re-lint and re-screen.
- **Replay:** `Diagonalization/NTimeHierarchy`, then the `Diagonalization` facade, into a copy of
  `oleans-lx2`.

**Decisions for the user:**
1. **UN-1's route.** Either:
   - **(i)** an API PR to `Build/Primitives.lean` (the maintainer's file) with
     `FinTM.pairExtractTM_fst_run` and its budget corollary. The draft is verified in the full
     file. Then the continuation keeps the five imports; or
   - **(ii)** authorize `import TCSlib.Complexity.SpaceComplexity.Machines.Clean` and route the
     extractor through `cleanTM`, sharing U2-S's cleaned bundle once promoted.

   Option (i) is smaller and keeps one proof per argument. The promotion candidate "header
   first-component pass with cleanup" (R's startup, B5a's H1) needs it either way.
2. **F2's cast-indexed `bufferedSecondCfg` pair** (shared with U2-S). Add it to the same or a
   separate API PR before either continuation is issued.

**The C1-UN continuation brief should:**
- re-base after the API PR(s);
- carry `un_universal_of_setup` if it was not landed;
- prescribe:
  - the setup's phases in order (capture with `embedSilentRetTM` or `capture_run`; `expandTM` to
    `ι jR`; buffer and scratch cleanup by `skipTM` → `skipBackTM` → `clearTM`;
    `FinTM.timed_rewind`);
  - the ledger without `|x|`;
- tighten rule 4's wording: independent phases continue.

**Environment (brief).** Unmodified Lean failed ("failed to locate application"). The addendum's
shim matched (`985924ad…`).
- The unrestricted `lake exe cache get` filled the disk (ENOSPC), and the first bootstrap died
  with a bus error at `ChoiceWords`.
- Recovery restored the pinned dependency copy. A targeted retrieval of the 33 direct Mathlib
  imports followed, with the cache, `TMPDIR` and oleans in `/dev/shm`.
- 10,858 byte-identical cache files were replaced by symlinks to the pinned cache.
- No `lake build` was run. The addendum's disk preflight and staged bootstrap
  (`../c1-writer-fill/REVIEW.md` (d)) would have avoided the first failure.
