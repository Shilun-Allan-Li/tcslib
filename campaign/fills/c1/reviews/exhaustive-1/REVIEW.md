# Review: C1-E fill delivery (the exhaustive replay), environment-blocked partial

Reviewer: the maintainer's read-only review sub-agent, 2026-10-17. All evidence is under
`review/c1-exhaustive-fill/` (`out/` holds the saved command outputs, `checks/` the probe files,
`scripts/` the reviewer's own scripts). Nothing in the main repository's working tree, its
branches or any existing worktree was modified. The only additions are the review worktree
`$S/wt-rc1x` (detached, now at the delivered head) and the ref `refs/review/c1-exhaustive`.

**Not clear to merge: this is an environment-blocked partial (phase 0). The target is still
`sorry`. Do not land it; carry its content into C1-E cont1 (see (f)).**

## Inputs

| Item | Value | Evidence |
|---|---|---|
| Delivery zip | `infra_local/fill-c1-exhaustive.zip`, SHA-256 `c7e33d5e…4b2e74`, 11 members | `out/00-inputs.txt`, `out/02-zip-listing.txt` |
| Extracted copy | `$S/incoming/c1-exhaustive/`, every member byte-identical to the zip | `out/02c-zip-vs-extracted.txt` |
| Brief | dispatch copy SHA-256 `4807189d…0b40535`. It equals the base's `briefs/c1-fill-exhaustive.md` (and the `wt-hk` copy) after the `@ANCESTOR@` substitution | `out/24-brief-addendum.txt` |
| Addendum | SHA-256 `a25474c5…8d2928`, byte-identical to the base's `briefs/fill-environment-addendum.md` | `out/24-brief-addendum.txt` |
| Base | `83ec6348b325f060cec2a917b45a4eda6e301d84`. It has no `.lean` diff against `6d18902f` | `out/00-inputs.txt`, `out/03-bundle.txt` |
| Olean snapshot | `$S/oleans-lndnf` | `out/10-…`, `out/11-…` |
| Delivered head | `070b5b83d37e6adf291dfa0d1ee703c9f774e72c` | `out/03-bundle.txt` |

## (a) Integrity and scope

**Integrity: PASS.**
- `SHA256SUMS`: all 10 listed members are OK (`out/01-sha256sums.txt`). The shim source
  `evidence/runtime/executable-path.c` has SHA-256 `985924ad…34fba7` and is byte-identical to the
  addendum's listing (`out/24-brief-addendum.txt`). It was not compiled or run.
- `git bundle verify` is okay. The bundle has one ref, `refs/heads/fill/c1-exhaustive` →
  `070b5b83…`, and its only prerequisite is `83ec6348…`. The head was fetched to
  `refs/review/c1-exhaustive`. Its sole parent is exactly the base, `base..head` is one commit,
  and the hash matches REPORT.md (`out/03-bundle.txt`).
- Patch, bundle and file agree (`out/05-patch-agreement.txt`):
  - The delivered `.lean` file equals the head blob (SHA-256 `cdb5bfab…57e1`).
  - The patch applies cleanly at the base, and base + patch equals the delivered file.
  - The patch-id of the patch equals the commit's (`f6654067…`).
  - A regenerated `format-patch` body is identical.

**Scope: PASS.** One file changed, 13 insertions and 1 deletion (`out/04-diff.txt`):
- **Region (a):** exactly `ChoiceReplay`, `Build.StepClock` and `Build.Seam`, after line 7. These
  are the brief's three imports, verbatim. The head file equals the pre-ship overlay
  (`audits/evidence/c1-fill-exhaustive/ExhaustiveReplayOverlay.lean.txt`) except for the appendix
  (`out/07-overlay-vs-head.txt`).
- **Region (d):** the "Fill appendix (C1-E)" paragraph. It sits before the docstring closer,
  which now has its own line, as the brief requires.
- **Unchanged:** regions (b) and (c), the statement, the consumer, and the module header and
  docstring.
- **Line widths:** the widest added line has 94 characters. The file has no line over 100,
  `git diff --check` is clean, and the file grew from 110 to 122 lines (`out/06-line-widths.txt`).

**The imports elaborate and create no cycle, but they do change the replay closure:**
- The import graph has 0 cycles at the base and at the head (`out/08-import-closure.txt`).
- It also has 0 cycles at the in-flight tips `origin/lean/nd-api-r2` (#122) and
  `origin/lean/ntime-diag` (#121 r2). None of the three new modules imports `ExhaustiveReplay`
  transitively (`out/09b-cycle-check-inflight.txt`). Neither in-flight branch touches
  `ExhaustiveReplay.lean` (`out/09-inflight-branches.txt`).
- The set of modules downstream of the file is unchanged: only the `TCSlib.Complexity.ClassNP`
  aggregator, plus the root.
- **The closure grows by 7 modules:**
  - The owned file's upstream closure goes from 16 to 29 modules. The replay closure (upstream
    closure, plus everything downstream with its own upstream closure, without the root) goes from
    **70 to 77**.
  - The 7 new modules are `Build.Catalog`, `Build.Contract.Basic`, `Build.CounterLoop`,
    `Build.Scan`, `Build.StepClock`, `ChoiceReplay` and `SymbolLift`.
  - At the head, the closure equals the brief's 77-module order list exactly, in both directions.
  - The aggregator's own closure goes from 69 to 76 modules.
  - All 8 modules involved were already in the root `TCSlib` closure, so the whole-library build
    set is unchanged (`out/14-root-closure.txt`).
  - Consequence: if the imports land, `ExhaustiveReplay` and the aggregator join the downstream
    replay set of every change to those 7 modules. For example, #122 edits `Build/CounterLoop`.
- **The aggregator's environment is consistent:** a check file with the aggregator's imports plus
  the three new ones elaborates with 0 errors and 0 warnings (`out/15-aggregator-env.txt`).
- **Appendix accuracy:** accurate. Each of these statements matches the logs:
  - only the three imports were added;
  - Lean starts with the fallback;
  - no draft is included;
  - the continuation sketch matches the brief's route.

  One nuance: the appendix attributes the failure to resource pressure alone. The logs also show
  cache and configuration failures (see (d)), and REPORT.md itself calls the resource cause an
  inference. The appendix is status narrative inside a public docstring, so it must not land as
  written.
- The REPORT's other source-level claims reproduce at the head:
  - lint: `0 FAIL, 15 WARN over 21 files`, identical to the delivered lint block
    (`out/17-lint.txt`);
  - the baseline list of 19 sorries equals `audits/logs/c1-fill-exhaustive-base-sorries.txt`
    (`out/16-screen.txt`);
  - a v3 screen re-run at the head gives 278 declarations, 106 pairs and 36,004 characters,
    byte-identical to the screen base, and no pair involves `ExhaustiveReplay.lean`
    (`out/16-screen.txt`).

## (b) Elaboration

| Run (against `oleans-lndnf`) | Result | Evidence |
|---|---|---|
| Base `ExhaustiveReplay.lean` | exit 0. Only warning: `61:8: declaration uses 'sorry'` | `out/10-elab-base.txt` |
| **Head `ExhaustiveReplay.lean`** | **exit 0, 0 errors. Only warning: `73:8: declaration uses 'sorry'`** (the same target, shifted by 12 lines). Sorry count: 1, same as the base | `out/11-elab-head.txt` |
| `C1ExhaustiveImportProbe` (verbatim base input) | exit 0, 0 errors, 0 warnings, 61/61 names resolve | `out/12-probe-verbatim.txt` |
| Delivered file plus the 61 `#check`s, in its own context | exit 0, 0 errors, 61/61 resolve; only warning is the target's `sorry` | `out/13-probe-headctx.txt` |

So the delivered head meets final check 1 for a partial: zero errors, and exactly the open
declaration's sorry warning. The worker could not show this; this review establishes it.

## (c) Draft/plan

REPORT.md contains **no proof text**. Drafts were "explored in scratch" but not shipped, so there
was nothing to probe from the delivery. Instead, the review checked the outstanding obligations
against the brief's route and probed the purely semantic and arithmetic parts of phase 4, plus the
precondition that phase 1 needs.

The probes are in `checks/C1ReviewProbes.lean`, which uses the delivered file's exact import
context. They read other files' definitions only through published lemmas, with no unfolding.
Result: **exit 0, 0 errors, 0 warnings, 0 sorry**, and every axiom print is within
`[propext, Classical.choice, Quot.sound]` (`out/18-probes.txt`). The first run's only failure was
the unknown name `smul_eq_mul` in P4, fixed by a `change`.

| Probe | Statement | Covers |
|---|---|---|
| P1 `xrProbe_not_haltsWithin_zero` | `¬ N.tm.HaltsWithin z 0` | REPORT's edge-case note, confirmed (see (e)) |
| P2 `xrProbe_window_stepWith` / `_runWith` | after a branch of length `|w|` from `initCfg z`, every work head is within `|w|`, every cell beyond radius `|w|` is blank, and `output.length ≤ |w|` | the **support argument** phase 1 needs. REPORT lists it as "still need checking"; it is derivable now |
| P3 `xrProbe_accepts_iff_of_halts` | at an all-halting depth `L ≤ T`, `AcceptsWithin z L ↔ AcceptsWithin z T`, by truncation with `runWith_append` and `runWith_of_halt` | phase 4, "agreement of the two acceptance bounds" |
| P3' `xrProbe_first_depth` | the first all-halting depth exists, is ≥ 1 and ≤ `T`, and answers as `T` does (`Nat.find`) | phase 4, first-depth termination |
| P4 `xrProbe_ledger` | `Σ_{L ≤ T} 2^L·A(L+1) ≤ (A+3)·2^{(A+3)(T+1)}` | phase 4, the docstring's ledger shape (the per-replay constant `A` is still open) |

Names cited outside the brief's 61-name list are public and in the head closure:
`NDTM.stepWith_of_some`, `NDTM.stepWith_of_halt` and `workTapePos_apply_le` (`out/18-probes.txt`).
The v3 screen of the probes against `SpaceComplexity/ExpBFS/Radius.lean` and
`ClassNP/Nondeterminism.lean` finds 0 pairs (`out/22-screen-probes.txt`).

**The stated obligations, checked against the brief's route.** REPORT's phases 1–4 match the
brief's phases. The following machine-level obligations are real at the base but not explicit in
either document. The continuation brief should name them:
1. **The clock consumes its counter.** After either exit the counter tape holds `w'`, and only
   `|w'| = |w|` is specified (`out/23-base-facts.txt`). A value-`L` word therefore has to be
   restored before every replay, not just once per depth. The framed `copyTM_run_ofCfg` is
   allowed; `copyTM_run` is one of the six barred R3 rows.
2. **The choice head ends at some `p ≤ τ`** (`replayTM_runFrom`'s `∃ p ≤ t`). It must be rewound
   before `incrementTM_run_succ_ofCfg` and before the next replay, whose lemma starts at head 0.
3. **The capture tape** holds `bufferTape (pre ++ output)` with its head at the end
   (`embedSilentCfg_cap`). The `[true]` test reads it, and it needs clearing too. P2's bound
   `output.length ≤ τ ≤ L` puts it inside the radius-`L` window.
4. **The window clear covers `[-L, L]`** on each of `N`'s work tapes (heads can sit at negative
   positions) and must return every head to 0, because the replay lemma's precondition is
   `initCfg` up to the choice tape. The input head returns by `timed_rewind`.

## (d) Environment

What failed, from the logs:

| # | Failure | Log lines |
|---|---|---|
| 1 | Unmodified Lean 4.25.0 failed with `error: failed to locate application`, the addendum's condition. With the exact shim, Lean starts (`Lean (version 4.25.0, x86_64-unknown-linux-gnu, …)`). **This part worked as designed.** | bootstrap.log 3–7, 19–20 |
| 2 | **Disk exhaustion.** A dependency-cache copy filled the shared filesystem. Later, 1.72 GB (8,684 files) were deduplicated, and 4 unused packages were left MISSING | 29–36, 46–50 |
| 3 | **Invalid compiled Lake configuration**, most likely a stale `lakefile.olean` truncated by the interrupted copy. `lake exe cache get` failed with `error: compiled configuration is invalid; run with '-R' to reconfigure`. Its internal `lake -v build --no-build proofwidgets:release` validation failed with `Failed to validate ProofWidgets cloud release`. Reconfiguring did not fix it, because the cache tool's internal call does not pass `-R` | 51–58, 63–69 |
| 4 | **Missing Mathlib oleans.** The first bootstrap module failed with `object file …/Mathlib/Data/Fintype/BigOperators.olean … does not exist`. The worker then restored 115 missing modules with the cache tool's `lookup` and `leantar`, a fallback the addendum does not authorize (disclosed) | 61, 71–74, 88–93 |
| 5 | **Memory starvation.** After the restore, `lean …CNF.lean -o …` sat without diagnostics "for several minutes". The cgroup counters: `memory.max 8589934592`, `memory.current 8589824000` (about 107 KiB of headroom), `oom_kill 1`, and the disk at 960 MiB free after earlier reaching 100% | 95–107 |
| 6 | **The final sweep.** With a 30 s per-module timeout, the first module, CNF, exited with 124 (timeout). The owned file, the import probe and the axiom prints then failed on missing upstream oleans (`final-oleans/…/NTIME.olean`, `…/ExhaustiveReplay.olean`). These are consequences of 5, not independent faults | final-sweep.log 3–25; axioms.log 7–14 |

**Root cause.** The worker ran on a shared host with an 8 GiB cgroup that was already at its
ceiling, and on a nearly full shared filesystem:
- **Memory:** a Lean elaboration mmaps its whole import closure. On a healthy host, CNF takes
  1.4 s at 1.39 GB maximum RSS, the owned file 1.3 s at 1.54 GB, and `Build/Catalog` (the largest
  of the 77 modules, at 13,241 lines) 41 s at 2.42 GB (`out/19-memory.txt`,
  `out/20-memory-catalog.txt`). With about 100 KiB of headroom, the import pages thrash, so a
  1.4 s job stalled for minutes. The `oom_kill` count shows the cgroup was already killing
  processes.
- **Disk:** a bootstrap needs about 6.1 GiB of packages (the Mathlib build alone is 4.7 GiB), plus
  about 0.2 GB of TCSlib oleans per output tree (77 modules, measured), plus the clone. The disk
  exhaustion is also the likely origin of failures 3 and 4.
- **Neither the source nor the shim is implicated.** Both elaborate here, and the shim did its
  one job.

**Proposed addendum changes for the continuation** (a new section, "Resources and cache", for
every fill brief):
1. **A resource preflight with a stop rule.** Before any cache or Lean work, record `nproc`, the
   cgroup's `memory.max`, `memory.current` and `memory.events`, and `df -h` for the clone and
   scratch filesystems.
   - Require at least 4 GiB of memory headroom, which is about 1.6 × Catalog's 2.42 GB peak, and
     at least 10 GiB of free disk.
   - If either is short, stop immediately with escalation **E-RES**, quoting the counters. Do not
     copy caches, deduplicate files or retry. Re-check the counters if a module stalls.
2. **One cache per clone.** Run `lake exe cache get` once into the clone's own `.lake/packages`,
   and do not copy dependency trees between directories. If the host already has a populated
   cache at the same pins, symlink `.lake/packages` to it instead, as the maintainer's replays do.
3. **Recovery from an invalid configuration.** On `compiled configuration is invalid`, delete the
   clone's compiled configurations, which can be regenerated and are not sources:
   `.lake/lakefile.olean*` and `.lake/packages/*/.lake/lakefile.olean*`. Then rerun
   `lake exe cache get` exactly once.
   - Say explicitly that the cache tool's internal `lake build --no-build proofwidgets:release`
     validation is expected and allowed. It is not a `lake build` under the ban.
   - If it still fails, stop with E-RES. Either authorize the hash-keyed `lookup`/`leantar`
     restore as a recorded fallback (list the commands and the module count), or forbid it. It
     should not stay undefined.
4. **No short per-module timeouts.** Drop them; the worker's 30 s timeout cannot tell a stall from
   work. Instead:
   - log each module's start and end time and `/usr/bin/time -v` (maximum RSS and major page
     faults);
   - expected figures on a healthy host: CNF about 1–2 s and 1.4 GB, Catalog about 40 s at `-j4`
     and 2.4 GB;
   - stop rule: if CNF has not finished within 10 minutes, report E-RES with the counters.
5. **A staged bootstrap** (a brief-side change):
   - **Before proof work**, bootstrap only the owned file's upstream closure plus the owned file:
     30 modules, 39,237 lines. This set is closed under imports, so the order list filtered to it
     stays in dependency order.
   - **At the final sweep**, run the other 47 modules (49,969 lines; the largest are
     `CookLevin/Hardness` at 8,783 and `Build/Primitives` at 6,886). They exist only to
     re-elaborate the `ClassNP` aggregator, which imports but contains nothing
     (`out/21-order-split.txt`).

   In the current order list, those 30 modules are interleaved with 24 of the others in the first
   54 lines.
6. **Keep the shim rules.** They worked: the exact SHA, preloaded only into Lean/Lake processes.

## (e) Other escalations

- **"The window clear is pending": true at the base.** No public row clears a radius window:
  - The framed `clearTM_run_ofCfg` (allowed; `clearTM_run` is barred) needs a delimited word
    `bufferTape w` on `[-1, |w|]` (`Catalog.lean:1520–1524`). It cannot handle interior blanks or
    content to the left of the head, as REPORT says.
  - C1's design already records "window clear [missing]" (`C1-design.md:240`).
  - Both are in `out/23-base-facts.txt`.
  - It is the worker's own pending private row and a promotion candidate, as the brief planned.
    It is not an API gap.
- **The support argument it relies on: no published run-level lemma in the context, but no gap.**
  - The only public statement of the window step is `Complexity.ExpBFS.inWin_stepWith`
    (`SpaceComplexity/ExpBFS/Radius.lean:70`). It is stated over `Cfg.InWindow` (`Build/CfgRecord`)
    and proved by unfolding `NDTM.stepWith`. Both files are outside the authorized import context
    (`out/23-base-facts.txt`).
  - The fact is nevertheless derivable from published one-step equations: P2 compiles. **No
    missing equation needs drafting.**
  - The continuation should add `NDTM.stepWith_of_some`, `NDTM.stepWith_of_halt` and
    `workTapePos_apply_le` to its probe list.
  - It should name `inWin_stepWith` as a known hazard: follow it, never transcribe it. P2 screens
    at 0 pairs against it.
  - Optionally, the maintainer's dedup window could promote a run-level `NDTM` window lemma to
    `Nondeterministic` to serve both files.
- **The T = 0 case is vacuous: confirmed, and the brief's edge-case bullet is wrong.**
  - `Cfg.init` sets the state to `some q₀` (`Configuration.lean:230–231`), so no branch of length
    0 halts (P1 compiles). The deepening's first all-halting depth is therefore ≥ 1 (P3').
  - The brief's bullet "`T = 0`: … `N`'s initial configuration is already halted, and `E` answers
    at depth `0`" (brief line 168) describes an impossible case. The continuation should restate
    it as vacuous.
  - The worker correctly flagged this without changing the statement.
- **No other gaps:** every brief-cited name resolves (61/61), and the clock, replay, embedding and
  phase-host contracts are as the brief describes them. The machine obligations in (c) items 1–4
  are construction work, not missing API.

## (f) Recommendation

1. **Do not land this delivery** (default policy for an environment-blocked partial). Its content
   is three imports and a status appendix. The appendix should not land in a public docstring
   either way.
2. **Pre-authorize the imports in C1-E cont1; do not have the maintainer land them separately.**
   They are fully verified here: the head elaborates, the probe resolves 61/61, there is no cycle
   at the base or at the #121/#122 tips, and the aggregator's environment is consistent. A
   standalone 3-line Lean PR would cost a PR plus a gate (zone revision rule) and gain nothing
   until the fill exists. It would also put `ExhaustiveReplay` and the aggregator into the replay
   set of in-flight `CounterLoop` work early (#122).

   Keep region (a) as "exactly these three imports". Re-run the overlay and the 61-name probe at
   the continuation's new base. The order list (77) already assumes these imports.
3. **Carry into cont1:**
   - REPORT's four-phase plan, and its edge-case note (correct the brief's `T = 0` bullet to
     "vacuous; the first all-halting depth is ≥ 1").
   - The four explicit machine obligations in (c):
     - restore the clock counter before each replay;
     - rewind the choice head;
     - read and clear the capture tape;
     - clear the window `[-L, L]` and return the heads to 0.
   - The maintainer-probed drafts P1–P4 (`checks/C1ReviewProbes.lean`), offered as optional
     `xr_` privates. They cite only public names plus the three additions above.
   - Add `SpaceComplexity/ExpBFS/Radius.lean` to the screen population, as the window-support
     hazard.
4. **Environment:** issue the addendum changes in (d) (preflight with E-RES, one cache, the
   configuration-recovery rule, no short timeouts, a staged bootstrap) with cont1. Dispatch cont1
   only to a host that passes the preflight: at least 4 GiB of memory headroom and at least 10 GiB
   of free disk.
