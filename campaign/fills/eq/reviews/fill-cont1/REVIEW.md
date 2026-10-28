# Review — E-Q cont1, the stage query's main machine (`Turing.NTimeDiag.exists_queryTM`, `Diagonalization/NTimeDiagonalizer.lean`): `fill-eq-query-cont1.zip`, branch `refs/deliv/eq-query-cont1` at `e952bc50`

**Verdict: land with listed edits.** The delivery is complete and correct. `exists_queryTM` is
proved within `[propext, Classical.choice, Quot.sound]`, and nothing in the file outside
`exists_diagonalizer` reaches `sorryAx`. There are no blockers and no majors. Land it by a
maintainer PR with four tested landing edits (E1–E4), after the user takes decisions 1–5 below.

**Not yet clear to merge.** There is no PR, no replay and no fill gate yet, and decisions 1–5 are
open.

Severity counts: 0 blockers, 0 majors, 4 minors (F1–F4), 9 notes (F5–F13).

Read-only review by the maintainer's review sub-agent, 2026-10-28 (UTC). Every claim cites a saved
output under this folder (`out/NN-*`).

How the review was done:
- **The zip is data.** I extracted it with `scripts/zipextract.py` (regular files only) into
  `delivery/` and ran nothing from it. Its `REPORT.md` was read as claims to check.
- **Worker-supplied Lean.** I scanned the worker's extended import probe before elaborating a
  copy of it. It has only `import` and `#check` lines and comments (out/19-probe-scan.txt).
  Every other file I elaborated is my own (`probe/`).
- **Lean.** It ran only through `tools/leanelab.sh` (`scripts/elab.sh`), one elaboration at a
  time, against `oleans-lhh`. That snapshot is the base's Lean tree, and also the tip's for the
  owned file's 36-module closure (out/31-tip.txt). There was no build or cache command.
- **No screen run.** The pair analysis applies the v3 screen's extraction and tiling to the
  declarations involved (`scripts/tiles.py`).
- **Python** always ran as `python3 -I`, from `scripts/`, with paths as arguments.
- **One worktree:** `wt-head`, at the head, with the `.lake/packages` link. It is removed at the
  end.
- **Slips, none affecting a result:**
  - zsh read `$B:c…` as a history modifier, and did not word-split two argument lists. I redid
    those steps as bash scripts (`scripts/dispatch.sh`, `tiles_run.sh`, `refgrep2.sh`).
  - My first seal hit the CLI's 100-error cap in its controls. I replaced it with controls that
    log one info line each (`mkseal3.py`). The first outputs are kept as
    `out/16z-superseded-*`.

## What was delivered, in one paragraph

Region (b) gains 211 private declarations: 4,899 lines between `qy_query_of_main` and the
target's docstring.
- **Two leaves.**
  - `qyCmpTM`: a two-tape lockstep length comparator with an order verdict.
  - `qyEmitTM`: a repeating emitter of a tape word between two fixed words.
- **Everything else** is published rows and calls under phase hosts, plus arithmetic and layout
  lemmas.
- **The machines.**
  - `M₁ = qyM₁ κ` is the phase host of a setup, the locator, and the top and middle writers.
  - The kit `QyKit` holds the published install and input calls, the step clock over `f`'s
    released call, and the input seek.
  - `qy_main` is `hmain` verbatim.
- **Region (c)** is `exact qy_main hf hg` under the landed `suffices`.
- **Region (d)** is rewritten to "Proved." with a public-facing description.

Head: 5,402 lines, 22 public and 214 private declarations (the base had 498 lines, 22 and 3).

## Findings

| # | Severity | Where | Finding | Evidence | Fix |
|---|---|---|---|---|---|
| F1 | minor (public-facing text) | 22 docstring lines of region (b) (head 1000, 1197, 3049, 3176, 3395, 3535, 3542, 3905, 4019, 4023, 4208, 4392, 4601, 4669, 4692, 4722, 4757, 4826, 4918, 5096, 5207, 5255) | Campaign labels in new library text: "(checkpoint N)" in 17 docstrings, "(leaf L3, the unary compare)", "(leaf L6)", "(L2…)" twice and "(L6's three emissions)". They are also inconsistent: `qyCmpTM`'s docstring calls it "leaf L3", while REPORT calls it L2. The (d) paragraph and the path scan are clean | out/09-new-text.txt | **E1** removes all 22 (text only). Afterwards there are 0 label hits (out/28-land-checks.txt) |
| F2 | minor (semantic duplication) | `qy_bits_len_mono` (head 3224), `qy_lt_two_pow_bits` (head 3233) | Both are Mathlib facts in the owned file's closure, up to the published equation `Nat.size_eq_bits_len`: `Nat.size_le_size` and `Nat.lt_size_self`. The file already cites `Nat.lt_size_self` in `qy_ones_ge`. The proofs re-derive them through `qy_log_bits` and `Nat.log`. The worker's `exact?` probe could not find a rewrite-then-apply. The same statements also exist outside the closure: `Complexity.LogProg.length_bits_mono` (`SpaceComplexity/Machines/Bin.lean`, at the base) and `lt_two_pow_bits` (`Randomized/SpaceAmplifyPoly.lean`, `origin/main` only) | out/21-bits-dup.out (both one-liners elaborate; `exact?` fails on the other four `Nat.bits` and arithmetic statements); out/03-closures.txt (`Bin` not upstream) | **E3**: two-line proofs citing Mathlib. Tested: out/26, out/27, out/28. Record the `Nat.bits` family in the ledger (below) |
| F3 | minor (module header) | header line 69 | "`Turing.NTimeDiag.exists_queryTM` — the stage query in linear time (sorried; C1-E's first fill)" is false after the landing. The header is frozen for the worker, and the maintainer updates its status at integration (brief, "Owned regions") | head 69 | **E4**: "… in linear time (proved)." The header's other campaign labels are left to the deferred docstring cleanup |
| F4 | minor (route conformance; decision 2) | the setup's test `n ≥ 3`; the round's top test | The brief's route is binding where it names a row. It names the scan fold (`Turing.scanTM` with `scanFold`) for the setup's `n ≥ 3` test and for the power-of-two test. The worker uses neither. `n ≥ 3` is the private comparator on `1^{n+1}` against the rung `1^3`. The power-of-two test is dropped: the next rung `2^{X⁴}` is built in unary when `X⁴ < \|bits n\|`, and compared with `1^{n+1}`. This decides `qy_decide_spec`'s three cases directly. Sound, no new leaf, disclosed in REPORT ("Route refinements"). The other refinements (below) use published rows where the brief allowed leaves | REPORT §"Route refinements"; head 2571–2604 (`qyLocM`'s phases); out/38-machines.txt | None in the code. Decision 2: ratify (recommended) |
| F5 | note (duplication; ledger) | `qy_run_one` (head 1250) | It is the one-step identity `M.runFrom c 1 = M.step c`, by `runFrom_succ_eq_step'` and `runFrom_zero` (85 characters). It is the source of 13 of the 20 new cross-file pairs, three of them copies by the brief's 90% rule (100%, 99%, 99%, all `SeamLayout`'s `sl_` proofs). The same idiom is inlined in `Catalog` (4), `Primitives` (4), `Loop`, `Encoding` and `SeamLayout` (3). It is stated privately in three files, not one as REPORT says: `ExhaustiveReplay`'s `xr_runFrom_one`, `SAT`'s `satRed_one` and `CfgRecord`'s `recordStep_runFrom_one`. No public statement exists. REPORT proposes `Deterministic` as the home, but that file is vendored (the lint's `VENDORED` list) | out/06-pairs-classified.txt, out/06-dup-tiles-cross.txt; `ExhaustiveReplay.lean:286`, `SAT.lean:1580`, `CfgRecord.lean:521` | Accept as landed: the brief's disposition for re-deriving other files' privates is "keep yours, and list it as a promotion request". Ledger: a public `MultiTapeTM.runFrom_one` in a TCSlib-owned module (for example `TuringMachine/Finite`, beside `runFrom_state_ne_none_of_le`), then re-point the five private and inline users. Not a blocker |
| F6 | note (in-file duplication) | `QyKit.bCl`/`bAbJ` (95%), `bCg`/`QyKit.K` (90%), `qy_transfer`/`qy_copy` (94%), `qy_clockHost_finish`/`qy_clock_start` (91%), `qy_two_pow_bits_le`/`qy_log_bits` (81%) | All 100 new in-file pairs are listed and justified. The four at 90% or more are bank one-liners by construction, the shared `copyMapTM`/`transferMapTM` endpoint conversion (tiles of 190 and 172 characters), and the shared `clockCfg` field conversion. One justification is inaccurate: `qy_two_pow_bits_le` re-derives `qy_log_bits`'s equation inline (`hsz`) rather than citing it, since it precedes it. Both came from the maintainer's route probe | out/06-dup-tiles-infile.txt; REPORT's in-file table | Accept as landed (in-file). Optional factoring in the dedup window |
| F7 | note (public names; rule 11) | `deriving DecidableEq, Fintype` on 7 private inductives | 22 → 22 public declarations at source. There are 88 new public constants: the 14 derived instances (`instDecidableEqQyCmp` …) and 74 compiler auxiliaries of those instances. No other new public constant. `workflow.md` §4 needs no finding for derived instances of a private type when a name check finds no clash. The `qy`/`Qy` names, and so these instance names, occur in no other `.lean` file on any of the repository's 430 refs (257 commits). The grep's control finds only the owned file, in 9 commits | out/34-generated.txt; out/22-rule11-refs.txt | None. The PR states "22 → 22 public declarations at source; 88 new public constants, all derived instances of private types and their auxiliaries" |
| F8 | note (scoping) | head 2249 | `attribute [local instance] QyKit.Qf QyKit.Qd QyKit.Sf QyKit.Sd` stays in force to the end of the namespace, which is the rest of the file: region (c) and E-D's `exists_diagonalizer`. It is harmless, since the instances fire only on `Fintype κ.Q`/`κ.S` goals. It is not one of the brief's named scoping commands (`section`, `open`, `variable`) | head 2249, 5402 | None. E-D's brief should mention it |
| F9 | note (records) | REPORT §"Promotion candidates" | The brief names four promotion candidates: "the clocked install call, L2, L3 and L6". REPORT omits the clocked install call (`QyClockSpec`, `qy_clocked_call`, `qy_clockHost_finish`/`_timeout`). L3 was not written, so it is moot | brief, Hosts; REPORT 641–657 | Ledger: add the clocked install call (below) |
| F10 | note (commit history) | all 8 commits | The subjects carry campaign labels ("E-Q cont1 checkpoint N: …", "E-Q cont1 finishing: …"). Two bodies name leaves "L2"/"L6", and every body ends with a `Claude-Session:` URL trailer | out/39-commit-messages.txt | Reword at landing as cp1's landing did ("NTimeDiagonalizer: …"; list below), keeping authorship. Decision 4 covers the trailer |
| F11 | note (docstring sync; decision 3) | the target's frozen `**Proof sketch.**` (head 5279–5297) | The frozen sketch still describes "fixed-degree binary arithmetic", a power-of-two test, writing `ℓᵢ₊₁` in binary and rejection "by a scan". The proof does the route note's unary arithmetic with cutoffs. `policy.md` §3 ("Synchronization") asks the sketch to follow the proof. The brief froze the docstring, and the (d) paragraph now describes the real machine | head 5275–5305; `policy.md` §3 | Decision 3: resync in the deferred docstring cleanup (recommended), or now by a maintainer docstring edit |
| F12 | note (proposed text) | REPORT §"Proposed Implementation paragraph" | The proposed paragraph cites private names (`qy_guard`, `qyM₁ κ`, `QyKit`, `qy_main`, …), which a public docstring cannot link. The landed (d) paragraph already says the same without them | REPORT 659–676 | Do not adopt it as written. If it is adopted later (F11), drop the private names |
| F13 | note (process) | the session | (a) The checkpoint zips cp2–cp7 are not in `exchange/inbox` (only the final zip is). The complete delivery supersedes them. (b) The inputs check (attachment hashes, ancestor check) is logged at 22:24:52Z, after checkpoint 2's commit (authored 22:13:12Z). It confirms the base, which is the branch's parent. (c) The two restarts: no two of the 264 logged Lean intervals overlap (the one apparent overlap is the same log shipped twice, `axiom-log.txt` = `axioms.out`). The interrupted `exact?` run is not logged. (d) The `exact?` probe's mechanics are sound (`first \| exact? \| sorry`; successes attributed in source order; one heartbeat timeout). It misses rewrite-then-apply duplicates (F2). (e) Searching all 174 PR heads, as a superset of the open ones, is fine | out/35-overlaps.txt; `logs/inputs-check.log`; inbox listing | None |

The route refinements, all within the brief's allowances (decision 2 ratifies F4 only):
- **L2 is a length comparator, not the binary `≤`.** `|bits F| > |bits n|` gives `F > n`.
  Otherwise `F ≤ 2n` and `F` is expanded to unary in `O(n)`. The case "`F > n` with equal lengths"
  is caught later, since `X − 1 ≥ F > n ≥ |bits n|`, so `2^{X⁴} > n`: interior. The comparator
  runs in `2·min(|u|, |v|) + 2` whatever `|bits F|` is, which is the brief's requirement.
- **L3's cutoff product.** The published install call of `computesFunInTime_polyUnary`, on
  `1^{X−1}`, replaces it. The call runs only after `X − 1 < |bits n|` is checked, so its cost is
  `O((L + 1)⁵)`.
- **L5 (`Nat.unpair`).** The pair `unpair h` is advanced each round by its successor rule (four
  lemmas). Its steps are the published `appendBit` install call, `clearTM` and the comparator.
- **The counter's tail** is the published `prepend` install call.
- **The top budget** is the published `polyBits` install call (`bits ((|y| + 1)²)`).
- **The stage code** is the `lengthBits` install call, as in the brief.

Every call is released at its entry (`seamReleaseTM`, read through `seamReleaseTM_runFrom_pos`).
The clock is `exists_stepClockTMVia`, not its `Bool` instance. There is no `vhostSilentTM`, R3
row, `callTM`/`emCall_*`, `xr_` or input-rewind citation (out/13a-walk-summary.txt). Only
`qyCmpTM` and `qyEmitTM` are hand-written transition tables. Every other machine is a phase host
over published rows, embedded calls and these two (out/38-machines.txt).

## What passes

### (a) Integrity and scope

| # | Check | Result | Evidence |
|---|---|---|---|
| 1 | Zip | SHA-256 `aa8e3ab1…1125e` as given; 113 members, no absolute, `..` or symlink member; 100 regular files extracted | out/00-zip-sha.txt, out/ziplist.txt |
| 2 | `SHA256SUMS` | 99/99 OK; every file but itself listed (paths `./`-prefixed; checker normalized) | out/01a-sums.txt |
| 3 | Bundle | `verify` okay; one ref `refs/heads/fill/eq-query-cont1` = `e952bc50` = `refs/deliv/eq-query-cont1`; sole prerequisite `43fe918f` | out/01-integrity.txt |
| 4 | Commits | 8 linear commits on the base, author `Claude`, touching only the owned file (+4,908/−4) | out/01-integrity.txt |
| 5 | Patches | patch-ids equal the commits'; each file equals this host's `git format-patch` except the trailing git-version line (`2.43.0` vs `2.50.1`) | out/01-integrity.txt |
| 6 | Source | `source/…/NTimeDiagonalizer.lean` = head blob `89f42530`; base blob `f965eac0` as the brief says | out/01-integrity.txt |
| 7 | Dispatch | the outbox brief `e44de76f…` = the base's repository copy with its 4 `@ANCESTOR@` := the base; the tip's copy is unchanged; the addendum v2.6 `9f5bd5e7…` at the base and the tip | out/02-dispatch.txt |
| 8 | Regions | 3 hunks: (b) an insert at base 376 (head 376–5274); (d) base 399–401 → head 5298–5305; (c) base 410 `sorry` → `exact qy_main hf hg`. The header, the twelve imports, every definition and law, and the three landed privates (base 1–375) are byte-identical, as are the target's docstring before (d), its statement and the `suffices`, and `exists_diagonalizer` with its docstring to the end | out/08-regions-hygiene.txt, out/07b-frozen-spans.txt |
| 9 | Hygiene of the added code | no `sorry`, `admit`, `axiom`, `set_option`, `open`, `section`, `variable`, `native_decide`, `aesop`, `delta` or `convert`. One `attribute [local instance]` (F8); ten `private instance`s; `unfold` only of own-file definitions (`QyKit.K`, `qySetB`, `qyRndS`, `qyLoc`, …). Widths at most 100 (no line of the file over 100); seven double blank lines (E2) | out/08-regions-hygiene.txt |

### (b) Statements frozen

- `declfreeze` v4, with the target's body authorized:
  - 22 → 22 public declarations, none added or removed;
  - "authorized body change: exists_queryTM";
  - 3 → 214 privates, none removed or changed.
- `privstmt`: no statement changed among the 25 base declarations.
- `stmtcheck` reports 25 missing lines, all `exists_diagonalizer`'s. That is an artifact of its
  in-order matching: it pairs the base's own `  sorry` with the head's later one. The direct
  comparison shows the span byte-identical (out/07-freeze.txt, note at the end).
- `qy_main`'s statement is `hmain`'s text verbatim, so `qy_query_of_main`'s `hM` takes it as is
  (head 5261–5265 and 347–352).

### (c) Elaboration and axioms

| # | Check | Result | Evidence |
|---|---|---|---|
| 10 | Head file, `oleans-lhh` | exit 0, 0 errors, exactly one warning: `5376:8 declaration uses 'sorry'` (`exists_diagonalizer`); 21 s, 2.35 GB | out/10-elab-head-lhh.out/.time |
| 11 | My axiom probe (head + `import Lean` + audit commands) | `exists_queryTM`: `[propext, Classical.choice, Quot.sound]`; 22 sampled privates within the standard three (`qy_writer_word`: `[propext]`). **All 1,323 local constants of the module are within the standard three except `exists_diagonalizer`** (`#eq_axioms_all`) | out/13-audit-head.out, out/13a-walk-summary.txt |
| 12 | The worker's axiom log | 212 prints, none outside the standard three, no `sorryAx`; its `QyAxioms.lean` is the head plus the appended prints only | out/13c-worker-axioms.txt, out/29-worker-derived.txt |
| 13 | Reachability | every one of the 211 new source-level declarations is reachable from `exists_queryTM` (no dead code), so every lemma's hypotheses are discharged in the final proof | out/23-reach-summary.txt |
| 14 | Sweeps (the worker's logs) | Bootstrap at the base: 84 modules in the order list's order, 0 errors, **20 sorry warnings in 9 modules, by name the base list**. Final sweep at `e952bc50`: 84 modules, 0 errors, 19 in 9 (the target's gone), `NTimeDiagonalizer` with no other warning (64.4 s, 2.66 GB). The non-sorry warnings equal the bootstrap's, module for module (326 in 18 modules, none in the owned file) | out/04-sweeps.txt |
| 15 | Import probe | the worker's `QyImportProbe.lean` (scanned: `import`/`#check` only), my copy: 0 errors, 0 warnings, 291 outputs. It covers 160 of the new code's 162 direct TCSlib constants; the other two are generated `_sizeOf_inst` instances | out/19-probe-scan.txt, out/19-probe-worker.out, out/18-probe-coverage.txt |
| 16 | Lint | `style_lint: 0 FAIL, 3 WARN over 5 files`: the base's two, and the owned file's size WARN (expected; file size is not a driver) | out/20-lint-head.txt |

### (d) Rule 10

The walk (out/13a-walk-summary.txt):
- It runs from every new local constant (1,276), stopping at the frozen declarations.
- It reaches 162 TCSlib constants of other files: 80 theorems, 60 definitions, 14 constructors
  and 8 inductives.
- The 60 definitions are 34 semireducible definitions, 10 instances and 16 projections. That is
  the worker's count exactly.
- No other file's private is reached; the only private names are the module's own matcher
  equations.
- No R3 row is reached.
- No TCSlib definition is reached only through a cited statement.

**My seal is maximal**, and I built it myself (`scripts/mkseal3.py`):
- `attribute [local irreducible]` on every TCSlib definition of the environment outside this
  module that is semireducible, not an instance, not a projection and not a matcher: 275, against
  the worker's 43. They include all 34 reached and all 29 the brief lists.
- `attribute [-simp]` on the environment's four `@[simp]` TCSlib definitions (`Action.apply`,
  `Cfg.init`, `MultiTapeTM.initCfg`, `NDTM.initCfg`).
- It is placed before the first new private (head 376).

**The body elaborates sealed with 0 errors**, and only `exists_diagonalizer`'s warning.

The controls log one info line each, so the CLI's cap of 100 errors cannot hide one:
- 275 `rfl` delta controls, 10 equation-lemma controls and 4 `simp` erasure controls;
- **all 289 fail sealed**;
- unsealed, 265 `rfl` controls close. The other 10 are structurally recursive definitions
  (`incFixed`, `decFixed`, `pairDecode`, …). Their generic delta goal does not close even
  unsealed, but their equation-lemma controls do;
- the 4 `simp` controls close unsealed;
- so every one of the 275 sealed definitions has a control that fails sealed and closes
  unsealed (out/16-seal-summary.txt, out/16-seal3-*.out).

The worker's seal (43 definitions and 4 erasures, in `QySealed.lean`: the head plus the
attribute block only) is sound and is contained in mine (out/29-worker-derived.txt).

**The inspection** (`scripts/tacargs2.py`, `classify.py`) classifies 2,949 tactic-argument rows
and 466 identifiers, resolved in the module's namespace (out/14-tactic-args.txt, out/15-kinds.out):
- **`rw`/`simp`/`simp only`/`dsimp`/`unfold` lists:**
  - no other-file TCSlib definition;
  - the 45 other-file TCSlib names are all theorems (the worker's 45);
  - `unfold` and `dsimp only [...]` name only own-file definitions.
- **Core and Mathlib names flagged in lists:** `Function.update` at head 1341, 1364, 1373 and
  1396 occurs inside a `have` statement nested in a `rw` list, not as a rule (the worker says
  the same). `reduceCtorEq` is a simproc.
- **`show` steps:**
  - they name `Cfg.ofWords` and `phaseHostTM` (head 5014, 5113, 5220) to unfold the own `qyM₁`
    only, and the maximal seal proves neither is unfolded;
  - core and Mathlib reductions in `show`, which the 2026-10-23 scope allows, are `Fin.last`,
    `Function.update`, `Nat.bits` and `Nat.pair` (the four `unpair` successor lemmas, head
    3242–3285, reduced by its body).
- **The leaves** never unfold `step` or `Action.apply` (both are sealed).

### (e) Rule 11 and the addendum

- **Rule 11:**
  - no R3 row, in the walk or in the diff's added text;
  - no other file's private, in the walk or as a name prefix in the diff;
  - all 211 new privates are under `qy`/`Qy`, unused in any other `.lean` file on all 430
    refs (out/22-rule11-refs.txt);
  - the derived instances are F7.
- **Addendum v2.6** (out/24-environment.txt):
  - preflight: 4 CPUs; headroom 13.31 GiB (floor 4); 24.44 GiB free, then 22.03 after the
    toolchain (floors 12 and 8); ext4;
  - the store was logged before the fetch (absent);
  - 34 roots, equal to my computation at the base;
  - 1,003 files fetched, "Completed successfully!";
  - manifest PASS (11 present, 4 doc packages absent);
  - no empty olean; a cache probe of a root;
  - the bootstrap with per-module time and peak memory;
  - one Lean process at a time: no two of the 264 logged Lean intervals overlap (one apparent
    overlap is the same log shipped twice), and the
    screens (Python) ran beside the bootstrap and the final sweep as allowed (out/35-overlaps.txt);
  - no stop and no E-SERIAL.

### (f) Duplication

- **The before screen** is byte-identical to the screen base: 1,781 declarations, 2,165 pairs,
  758,766 characters.
- **The after screen** (`e952bc50`) has 1,932, 2,285 and 782,065:
  - 120 new pairs, 0 gone, every one with an owned-file declaration on a side;
  - 20 cross-file (the owned file is the target in 3 and the source in 17) and 100 in-file.
- **The first after screen** (`323e3588`) had 10 more pairs. The worker's factoring commit
  `e952bc50` removed them and added none (out/05-screens.txt, out/06-pairs-classified.txt).

The 20 cross-file pairs, by class (the tiles are in out/06-dup-tiles-cross.txt):

| Class | Pairs | Disposition |
|---|---|---|
| `qy_run_one`, the one-step identity (F5) | 13: `sl_unarySplit_copy` 100%, `sl_unarySplitTM_run` 99%, `sl_pairSkip_two_steps` 99%, `pairDiag_separator` 75%, nine at 71% (`Catalog`'s `f2_*` ×4, `Primitives` ×4, `Loop`) | accept as landed; promotion request to the ledger (a TCSlib-owned home, not the vendored `Deterministic`). Not a blocker: 85 characters of two published rewrites |
| `qyC_mapState`, the `Cfg.mapState` field-equation idiom around `Cfg.ext` | 4: `xr_halt_fixed` 83%, `exists_seamLayoutTM` 72%, `sl_rewrap` 70%, `xr_phase_step` 69% | accept: the accepted idiom class (this file's is a third, as REPORT says) |
| `qyEmitTM` against `FinTM.emitAction` | 66% (the fixed-word emission chain's shape) | accept: `emitAction` halts at its chain's end, so a phase host cannot continue from it to the scan |
| `qy_call` against `sl_rewrap` | 52% | accept: `seamReleaseTM_runFrom_pos` and the field equations |
| `qy_cmp_run` against `b2_unary_run` | 50% | accept: two `runFrom_succ_eq_step` tiles of a run lemma |

The semantic search:
- The worker searched by name and by statement on every ref, and ran `exact?` on 129 statements.
  It found and fixed one re-derivation: `QyKit.tape_cases` now cites
  `Classical.exists_or_forall_not`.
- My probe adds F2's two Mathlib one-liners. `exact?` still fails on `qy_two_pow_bits_le`,
  `qy_log_bits`, `qy_pow6_le` and `qy_ones_val` (out/21-bits-dup.out).
- **`ClassP/BinaryArith`** (#135, `main` only, not in the tree): its `le`/`lt` are
  function-level value comparisons in polynomial time, and its `mulU` is a unary product. Neither
  is citable at the base, and the fill writes no cutoff product. REPORT's ledger agrees.

**Ledger entries** for `campaign/duplication-ledger.md`, for the maintainer's dedup window (none
is a blocker; none needs a change before landing):
1. **The one-step identity** (F5): a public `MultiTapeTM.runFrom_one`. Its customers are
   `qy_run_one`, `xr_runFrom_one`, `satRed_one`, `recordStep_runFrom_one` and the 13 inlined
   uses (`SeamLayout` 3, `Catalog` 4, `Primitives` 4, `Loop` 1, `Encoding` 1).
2. **The `Nat.bits` arithmetic family** (F2):
   - `qy_two_pow_bits_le`, the same statement as `two_pow_bits_le` (`SpaceAmplifyPoly`, `main`);
   - `qy_log_bits`, whose `≤` half is `Bin`'s `length_bits_le_log`;
   - before E3: `qy_bits_len_mono` (= `Bin`'s `length_bits_mono`) and `qy_lt_two_pow_bits`.

   A shared `Nat.bits` module would remove the copies.
3. **Row candidates** (the brief's and REPORT's):
   - the clocked install call (`QyClockSpec`, `qy_clocked_call`, `qy_clockHost_*`; F9);
   - the length comparator with verdict (`qyCmpTM`, `qy_cmp_run`);
   - the repeating emitter (`qyEmitTM`, `qy_emit_run`/`_stop`);
   - the phase host's segment forms (`qy_hosted*`, `qy_round_of_seg`);
   - the `Nat.unpair` successor rule (`qy_unpair_succ_*`).
4. **In-file factoring candidates** (F6): the `copyMapTM`/`transferMapTM` endpoint conversion and
   the `clockCfg` field conversion. Optional.

### (g) Docstrings and policy

- Every one of the 212 declarations in regions (b) and (c) has a docstring.
- All 30 theorems with proofs over 20 lines carry a literal `**Proof sketch.**`. Five long
  definitions are definitions, not proofs (out/09a-docstrings.txt).
- **The leaves' docstrings say which public row they are not.**
  - `qyCmpTM`: `compareTM_contract` decides equality at `compareStop` with no order verdict, and
    `walkTM_run_ofCfg` reports nothing about the other tape.
  - `qyEmitTM`: no public row emits a tape word with repetition.
- **Attribution.** The target keeps its `[AB09, §3.2 …]` citation and the file its
  `## References`. The privates are implementation lemmas and need no source tag.
- **The (d) paragraph** is accurate and has no label (out/09-new-text.txt). The labels F1 found
  are the only ones in the new text, and there is no `audits/` or `campaign/` path.

## Landing edits (all tested)

`out/25-landing-edits.diff`, applied by `scripts/landing_edits2.py`. Every edit is asserted
against the head's exact text before it is applied. The edited file is
`probe/land/NTimeDiagonalizer.lean` (5,389 lines, SHA-256 `2e29f0d8…5f1e`).
- **E1** — the 22 label removals of F1 (text only; two shortened so that no line passes 100).
- **E2** — the seven double blank lines (head 630, 1027, 1183, 1652, 1896, 2250, 2531) become
  single.
- **E3** — `qy_bits_len_mono` becomes
  `rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len]; exact Nat.size_le_size h`, and
  `qy_lt_two_pow_bits` becomes `rw [Nat.size_eq_bits_len]; exact Nat.lt_size_self n` (F2).
- **E4** — header line 69: "(sorried; C1-E's first fill)" → "(proved)" (F3).

Tested on the edited file, against `oleans-lhh`:
- exit 0, 0 errors, exactly `5363:8 declaration uses 'sorry'` (`exists_diagonalizer`)
  (out/26-land-lhh.out);
- axioms: `exists_queryTM` within the standard three, and all 1,323 local constants except
  `exists_diagonalizer` (out/28-land-audit.out);
- the maximal seal: body 0 errors, the same 289 controls failing sealed and closing unsealed as
  at the head (out/27-land-seal-summary.txt);
- `declfreeze` base → landed: 22 → 22, only the authorized body change;
- head → landed: no statement changed; 22 privates changed in docstring or body only;
- frozen spans: only header line 69 differs from the base in lines 1–375 (out/28-land-checks.txt,
  out/07b-frozen-spans.txt);
- lint 0 FAIL, 3 WARN; widths at most 100; no double blank line; 0 label hits; every proof over
  20 lines still has its sketch (out/28-land-checks.txt, out/28-land-lint.txt).

E1, E2 and E4 change no code. E3 changes two proofs only; their statements and axioms are
unchanged. By the v3 screen's thresholds, E3 adds no pair (its new bodies share at most 46
characters with any population declaration, below the screen's 60) and removes the in-file pair
`qy_two_pow_bits_le`/`qy_lt_two_pow_bits` (out/28b-land-e3-tiles.txt).

**Commit subjects** (F10; keep authorship by `git am -3` or a cherry-pick of the series, then one
maintainer commit for E1–E4):

| Commit | Landed subject |
|---|---|
| `21dd053c` | NTimeDiagonalizer: the stage query's setup as a run of its phase host |
| `68a5d3f0` | NTimeDiagonalizer: one round of the locator as a Turing.Round |
| `12d94cdc` | NTimeDiagonalizer: the locator's loop and its linear ledger |
| `a1db58c7` | NTimeDiagonalizer: the input seek and the stage code in both writers |
| `258e3f1b` | NTimeDiagonalizer: the budget field and the writers |
| `ce0c8aca` | NTimeDiagonalizer: the main machine; exists_queryTM proved |
| `323e3588` | NTimeDiagonalizer: cite Classical.exists_or_forall_not; drop four unused privates |
| `e952bc50` | NTimeDiagonalizer: factor two in-file copies |
| (maintainer) | NTimeDiagonalizer: the stage query's landing edits (docstrings, the header's status, two Mathlib citations, blank lines) |

In the bodies of `21dd053c` and `258e3f1b`, also replace "L2"/"L6" by "the comparator"/"the
emitter".

## Decisions for the user

1. **The landing edits E1–E4.** Recommended: all four. E3 is the only one that touches code, and
   it is tested.
2. **The route deviation F4.** The setup's `n ≥ 3` test uses the private comparator instead of
   the named scan fold, and the power-of-two test is replaced by building and comparing the next
   rung in unary.
   - (a) Ratify as a sound refinement within the leaf allowance. **Recommended.**
   - (b) Require the scan fold. Not recommended: it would add a phase and a fold proof to replace
     correct, cheaper code.
3. **The frozen proof sketch F11.**
   - (a) Resync it in the deferred docstring cleanup, together with the header's labels.
     **Recommended:** it is gated text, and (d) already describes the real proof.
   - (b) Resync it now, by a maintainer docstring edit to this PR.
4. **The commit history F10.** Reword the subjects and the two bodies as listed. Keep or drop the
   `Claude-Session:` trailers: the user's call. **Recommended:** reword, keep `Co-Authored-By`.
5. **The duplication dispositions** (F5, F6, F2's outside copies).
   - (a) Accept all 120 new pairs as landed: the 20 cross-file by the classes above, the 100
     in-file as justified. Record the four ledger entries for the maintainer's dedup window.
     **Recommended.**
   - (b) Promote `MultiTapeTM.runFrom_one` by an API PR before landing. Not recommended: it is 85
     characters of two published rewrites, and five other files would re-point in the same
     window.

The REPORT's proposed Implementation paragraph is not adopted as written (F12). If decision 3(b)
is taken, its text without the private names is a starting point.

## Replay list for the landing PR

The owned file's downstream closure is 2 modules at the head and at the tip (out/03-closures.txt).
`NTimeHierarchy` imports `Build/NDHost`, which #174 changed. So chain from **`oleans-lnfapi4`**,
the tip's snapshot: the tip's Lean is #174's merge `c2887fb5`, with 0 `.lean` files changed since
(out/31-tip.txt). In order:
1. `TCSlib/Complexity/Diagonalization/NTimeDiagonalizer`
2. `TCSlib/Complexity/Diagonalization/NTimeHierarchy`
3. `TCSlib/Complexity/Diagonalization` (the facade; never the root `TCSlib`)

Expected:
- 0 errors;
- `NTimeDiagonalizer` with exactly `exists_diagonalizer`'s sorry warning;
- `NTimeHierarchy` and the facade with no sorry warning, as in the worker's final sweep.

Other facts for the landing:
- **The merge is clean.** The owned file is unchanged at the tip (blob `f965eac0`), and
  `merge-tree` of the tip and the head writes a tree with no conflict.
- **#175 is independent of this replay.** The SCP move (gate 86, `lean/scp-constructible`)
  changes only `SpaceComplexity/Constructible` and `Savitch`. Neither is upstream of any of the
  three modules, so its order against this PR does not change this replay's closure
  (out/37-pr175.txt).
- **Link `.lake/packages`** in the PR worktree.

## What the fill gate's pack should ask

Attach:
- `campaign/standards/TEMPLATE.md`, `policy.md` and `workflow.md`;
- the brief and addendum v2.6;
- the delivery's REPORT and evidence;
- this review with `out/`, and the landing diff.

Ask:
1. **Correctness:** the kit, the round, the loop's ledger and the writers; `qy_main` as `hmain`.
2. **Route conformance:** F4, and the refinements listed under the findings.
3. **Duplication:** F2, F5, F6 and the ledger entries.
4. **Rule 10:** the maximal seal (275 definitions, 4 erasures, 289 controls) and the inspection.
   Rule 11, and F7's public constants.
5. **The public-facing text** after E1 and E4; F11.
6. **The duplication screen at the landing head,** against the tip's screen base. E3 should add
   no pair and remove one in-file pair (out/28b-land-e3-tiles.txt).
7. **The replay** (3 modules from `oleans-lnfapi4`).
8. **Deliverable:** a downloadable `eq-query-cont1-fill-findings.md` with the findings table and
   the verdict line.
