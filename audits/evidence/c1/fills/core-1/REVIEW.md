# Review: C1-R (the interpreter core) fill delivery, `fill-c1-core.zip`

Read-only maintainer review, 2026-10-17. Target `Turing.exists_ndInterpreterCore`
(`TCSlib/Complexity/TuringMachine/NDCodeSimulator.lean`). All paths below are relative to
`$S/review/c1-core-fill/` unless absolute (`$S` = the session scratchpad). Each claim cites a
saved output under `out/`.

**Verdict.** This is an environment-blocked partial. Its bytes are intact and its scope is clean:
two authorized imports and a flagged appendix, with the target still `by sorry`. It elaborates
here with exactly the base's two sorry warnings. Two of the report's statements need correcting.
(1) The four "unchecked" helper drafts **elaborate verbatim, with no errors or warnings and
standard axioms**. (2) Escalation E1 is real, and #122's `counterValue_eq` fully resolves it. The
review also found one route gap that neither the report nor the brief raises (G2: the step
block's table and summary layout). It must be decided before the continuation is issued.

- **C1-R partial: not a merge candidate. Do not land it** (this confirms the default policy; see (f)).
- **C1-R cont1: not yet clear to dispatch.** It waits on three things: #122 merged and a fresh
  olean snapshot, the G2 route decision, and the environment addendum revision in (e).

## Inputs

| Input | Value | Evidence |
|---|---|---|
| Delivery zip | `/Users/seyoonr/phd_experiments/tcslib/infra_local/fill-c1-core.zip`, SHA-256 `860efb78…7645`, 32 members | `out/zip-listing.txt`, `out/zip-vs-extracted.txt` |
| Extracted delivery | `$S/incoming/c1-core/`, all 32 members byte-identical to the zip | `out/zip-vs-extracted.txt` |
| Brief (dispatch copy) | `infra_local/fill-dispatches/c1-fill-core.md`, SHA-256 `15a09e9c…9268`. Equal to the base's `briefs/c1-fill-core.md` once `@ANCESTOR@` is substituted | `out/brief-copies.txt` |
| Addendum | `infra_local/fill-dispatches/fill-environment-addendum.md`, SHA-256 `a25474c5…2928`, equal to the base's copy | `out/brief-copies.txt` |
| Base | `83ec6348b325f060cec2a917b45a4eda6e301d84`. The worker started from `2cce4804…`, a descendant with no Lean change | `out/initial-head.txt` |
| Olean snapshot | `$S/oleans-lndnf` | — |
| Review worktree | `wt/` (detached; at head `4061f282` after the base elaboration). Mathlib link as required | `out/bundle-integrity.txt` |
| Bundle head ref | `refs/review/c1-core` → `4061f2821c59982584f5f36fca5dd1090c92ec93`, in the main repo's ref store | `out/bundle-integrity.txt` |
| #122 (read only) | `$S/wt-ndapi2` @ `b6627401` (`lean/nd-api-r2`) | `out/pr122-inventory.txt` |
| Probes (mine) | `probes/DraftProbe1.lean` (the delivered file with the four drafts inserted verbatim at region (b)), `DraftProbe2.lean` (adds axiom prints, a used-constants dump and the extra `#check`s), `E1Probe.lean`, `C1CoreImportProbe.lean` (the base's probe, unchanged). Hashes in `out/probe-hashes.txt` | — |

No build command was run. Every Lean run went through `tools/leanelab.sh`, one at a time. The
delivered `executable-path.c` was compared byte for byte with the addendum's block. It was not
compiled or run. Python ran with `-I`, using my scripts under `scripts/`.

## (a) Integrity and scope

| Check | Result | Evidence |
|---|---|---|
| `SHA256SUMS` (31 entries; the 32nd member is the sums file itself) | all OK | `out/sha256sums-check.txt` |
| `git bundle verify` in a worktree at the base | okay. One head, `refs/heads/fill/c1-core` = `4061f282…`, one prerequisite = the base | `out/bundle-integrity.txt` |
| Head fetched into `refs/review/c1-core`; parents | sole parent `83ec6348…` (exactly the base). Author `OpenAI Codex` | `out/bundle-integrity.txt` |
| Commit hash vs REPORT.md | `4061f2821c59982584f5f36fca5dd1090c92ec93`, matches | `out/bundle-integrity.txt` |
| Patch vs bundle | Patch `From 4061f282…`. Its body equals `git diff base..head`, index line included (`544a6775..35ead8e9`). Applied to the base source, it reproduces the delivered file byte for byte | `out/patch-vs-bundle.txt` |
| Delivered `.lean` vs head blob | identical (SHA-256 `980e4cb5…`) | `out/patch-vs-bundle.txt` |
| Evidence cross-checks | `base-sorries.txt` equals `audits/logs/c1-fill-core-base-sorries.txt`. `screen-before` equals `audits/logs/c1-fill-core-screen-base.txt`, and `screen-after` equals `screen-before`. The shim source equals the addendum's | `out/evidence-crosschecks.txt` |

**Scope.** The diff touches one file and has 17 insertions and 1 deletion (`out/base-head.diff`):
- **Region (a):** exactly `import …Build.InputWindow` and `import …UniversalStartup`, after line
  8. They are the brief's two authorized imports. The import block equals the pre-ship overlay's.
- **Region (d):** the "**Fill appendix (C1-R).**" paragraph and a "**Proof sketch
  (continuation).**" paragraph at the end of the target's docstring, with ` -/` on its own line
  (line 143).
- No change to regions (b) or (c), the bridge, the replay canonizer, the header or the statement.
- 163 lines (base 147). 3 public and 0 private declarations. Two `sorry` tokens, as at the base.
  Maximum line width 97 everywhere (17 added lines, none over 100, no trailing whitespace).
  Evidence: `out/scope-widths.txt`.

**Replay closure.** The module's own upstream closure grows from 34 to 36 modules, adding only
`Build/InputWindow` and `UniversalStartup` (their own imports were already in it;
`out/closure-added.txt`). The only downstream module is the `TCSlib/Complexity/TuringMachine`
aggregator (`out/downstream-base.txt`), which already imports both. The replay set is therefore
unchanged: the upstream closure of {NDCodeSimulator@head, aggregator} has the same 80 modules at
base and head, and it equals `briefs/orders/c1-fill-core.txt` exactly (`out/replay-closure.txt`).
The imports create no cycle. At #122's head the downstream set is still only the aggregator
(`out/pr122-downstream.txt`).

**Appendix accuracy.** Accurate in substance:
- `counterValue` is a semireducible `def` with no published equation at the pin
  (`out/elab-e1-probe.out`).
- Passing `counterValue_bits` to `ht` would rely on unfolding it.
- Nothing was restated and no replacement loop was built.

Caveats:
- Lean's auto-generated `Turing.counterValue.eq_1` is present in the environment. It was created
  by `counterValue_bits`'s own `rw [counterValue]`. Using it would still be unfolding, so the
  claim stands.
- The appendix's last sentence describes this sandbox's bootstrap failure. That is campaign
  record, not library documentation, and it goes stale once #122 merges. This is another reason
  not to land it.

**Corrections to REPORT.md** (none affects integrity):
1. The report calls the drafts "not checked … may need elaboration repairs". In fact they
   elaborate verbatim at the delivered head with 0 errors and 0 new warnings (see (c)).
2. The report says the "attempted bootstrap still produced no fresh `Zone.olean`". But
   `evidence/bootstrap-union.log:2` reads `PASS 1 TCSlib/Complexity/TuringMachine/Build/Zone`. By
   the repository's `scripts/lean_check_tree.sh` pass rule, that means a fresh, non-empty olean. The run
   then stopped at `MODULE 2 …ChoiceWords` (line 3) and was terminated.
3. E1 is reported against the loop only. The window copier's statement reads the same
   expression: `let y := (z.drop p).take (Nat.ofDigits 2 (w.map Bool.toNat))`,
   `Build/InputWindow.lean:66` (`out/route-gaps-evidence.txt`). So phase 2 is blocked by E1 too.
   #122's lemma covers both uses.

## (b) Elaboration

| Run | Result | Evidence |
|---|---|---|
| Delivered head `NDCodeSimulator.lean` against `oleans-lndnf` | EXIT 0, 0 errors. Exactly 2 warnings, `declaration uses 'sorry'` at 93:8 (`exists_replayCanonizer`) and 144:8 (`exists_ndInterpreterCore`) | `out/elab-head.out` |
| Base `NDCodeSimulator.lean`, for comparison | EXIT 0. 2 sorry warnings at 91:8 and 128:8 (the same two declarations; lines shifted by the +2 imports and the appendix) | `out/elab-base.out` |
| The base's `C1CoreImportProbe` (77 `#check`s) in the head's import context | EXIT 0, 0 errors, 0 warnings, 77 resolved. Output identical (363 lines) to the pre-ship log's `C1CoreImportProbe.out`. This replaces the worker's failed re-run | `out/import-probe.txt`, `out/import-probe-raw.out` |
| Axioms of the target | `[propext, sorryAx, Classical.choice, Quot.sound]` (direct `sorry`) | `out/elab-drafts-axioms.out` |
| Style lint (`campaign_style_lint.py TuringMachine`) at head | `0 FAIL, 63 WARN over 79 files`, the same as the worker's `lint.log` and the base. NDCodeSimulator: 163 lines, 3/0 | `out/lint-head.txt` |

The sorry set is unchanged against the base: the same two declarations, and no new warning.

## (c) The drafts

`probes/DraftProbe1.lean` is the delivered source with REPORT.md's last ```` ```lean ```` block
inserted **verbatim** after the replay canonizer's `sorry` (region (b)). The insertion script is
`scripts/mkprobe.py`, and the extracted block is `probes/DraftProbe1.lean.drafts.txt`. Results:

- **Elaboration:** EXIT 0, no errors, and only the two existing sorry warnings
  (`out/elab-drafts-verbatim.out`). No repair was needed.
- **Axioms:** the first three drafts have `[propext, Classical.choice, Quot.sound]`.
  `ic_table_call` additionally has `sorryAx`, which comes only from the cited stub
  `exists_replayCanonizer`, as allowed (`out/elab-drafts-axioms.out`).
- **Constants used** (from a `getUsedConstants` dump of each proof term): only public `Turing.*`
  constants and the probe's own auxiliary proofs. No `.eq_N` or `eq_def` equation lemma of
  another file, no other file's private, none of the six R3 rows (`out/drafts-rule10-11.txt`).
  All four names carry the `ic_` prefix.
- **Lint, drafts included:** 261 lines, 3 public / 4 private. Still 0 FAIL / 63 WARN, with no
  other file's lint changed (`out/lint-drafts.txt`).
- **Copy screen v3, drafts included** (base's script, 7-file population): 175 declarations
  (171 + 4), still **19 pairs / 5,115 chars**. The pair lines are byte-identical to the delivered
  `screen-after.txt`, so no new copy (`out/screen-with-drafts.txt`).

| Draft | Compiles | Public API only / no unfolding | Duplicates a library lemma? | What remains |
|---|---|---|---|---|
| `ic_header_result` (either prefix pass: halted, output `bits t` or `α`, head at `4\|bits t\| + 2\|α\| + 7`, time `16\|bits t\| + 8\|α\| + 25`) | yes | yes. `prefixCanon_complete`, `pairExtractTM_fst/_snd`, `length_pairEncode`, `pairDecode_pairEncode`, core simp lemmas. Reads `prefixCanonTM` only through `prefixCanon_complete` | no. `prefixCanon_complete`'s only other consumer is the chapter-1 canonizer (`UniversalStartup.lean:344`). No pair-of-pair header split exists (`out/draft-dup-search.txt`, `out/draft-dup-search2.txt`) | Run it inside a fresh bank. The source's final work tapes have no published description, so its residue must be framed and never read. This is the promotion candidate UN and B5a's H1 also need |
| `ic_capture_return` (bounded run → first halt `u ≤ T` → R1′ capture at the live anchor, no earlier anchor) | yes | yes. `exists_first_halt`, `MultiTapeTM.initCfg_eq`, `Cfg.init_state`, `embedSilentRetTM_run`. It passes `¬(…).Halted` as `state ≠ none` through the reducible `abbrev Cfg.Halted`. The gated host does the same (`Build/StepBlockLoop.lean:333`, `out/halted-precedent.txt`) | no public lemma. The same first-halt + R1′ pattern is written inline in privates (`Build/CertShell.lean` `certCore_run`, `SpaceComplexity/Inclusions.lean:799–809`). Promotion candidate, as the report says | Instantiate twice (two fresh banks) and seam with `seamCompTM_run_ofCfg` and the rewind |
| `ic_replay_window` (replay of any `r ≤ t` prefix on `x.take t` = branch on `x`, state and output) | yes | yes. `replayTM_runFrom`, `runWith_initCfg_take`, `withChoiceTape_state/_output`, `List.length_take` | no (`replayTM_runFrom` has no consumer yet) | Covers both clauses' semantics (r = t, and r = t′ for the prefix clause). Also needs `(pairEncode u x).drop (2\|u\| + 2) = x` for the window's `y` |
| `ic_table_call` (clean install call of the replay canonizer, cost depending on `α` only) | yes | yes. `exists_replayCanonizer` (cited stub), `FinTM.exists_installCallTM` | no | **Installs the whole `serializeK`, which is not the layout the loop needs. See G2.** It will probably change, for example to install `tableBitsK …` instead |

**Rule 10 bookkeeping for the continuation.** The drafts cite 12 external public names outside
the brief's 77-name probe, plus the owned file's `exists_replayCanonizer`
(`out/draft-citations-vs-probe.txt`). Their statements also mention `pairEncode`,
`FinTM.bufferTape` and `NDTM.runWith`, which the target's statement already uses. Each name
resolves in the head's import context (`#check`s in `out/elab-drafts-axioms.out`):
- `FinTM.pairExtractTM`, `pairDecode_pairEncode`, `MultiTapeTM.exists_first_halt`,
  `MultiTapeTM.initCfg_eq`;
- `embedSilentRetTM`, `embedSilentRetTM_run`, `embedSilentCfg`;
- `NDTM.replayTM`, `NDTM.withChoiceTape`;
- `stateWord`, `serializeK`, `Cfg.Halted`, `exists_replayCanonizer`.

The verdict and the ledger will also need the public `outputSummary_true` (`Build/StepBlock.lean:153`) and
`length_bits_le_self` (`Encoding.lean:286`) (`out/route-gaps-evidence.txt`). The continuation's
probe should list all of these.

**Ledger.** I checked the report's conditional arithmetic by hand:
- One pass: `3|u| + 4 + 5(|u| + 1) = 16|bits t| + 8|α| + 25`, with `|u| = 2|bits t| + 2 + |α|`.
- The suffix position, the rewind bound and the `36|bits t| + 18|α| + 59` total are correct.
- Both final inequalities hold with `C = a + b + w + 50(L + 1) + 10`, given the window bound
  `w(min(t, |x|) + 1) + 2|bits t|`, the loop bounds and `length_bits_le_self`.

The ledger stays conditional, as the report says: `a`, `b` and `w` are not constructed.

## (d) Escalation E1 and other API gaps

**E1 is true at the base, and #122 is sufficient** (`out/elab-e1-probe.out`, `out/e1-counterValue-grep.txt`):
- **At the base:**
  - `Turing.counterValue_eq` and `Turing.codeBitsNat_eq` are absent.
  - `counterValue` is a semireducible `def`.
  - `hostedLoopTM_run`'s `ht` is `Nat.ofDigits 2 (w.map Bool.toNat) = t` (`Build/StepBlockLoop.lean:435`).
  - `Mathlib.Data.Nat.Digits.Lemmas` is not imported, so `Nat.digits_two_eq_bits` is unavailable,
    as the report says.
- **With #122's statement declared locally (identical `:= rfl`), everything goes through by
  rewriting with published lemmas only:**
  - the loop's `ht` for `w = bits t`, as `(counterValue_eq _).symm.trans (counterValue_bits t)`
    or `rw [← counterValue_eq]; exact counterValue_bits t`;
  - the window copier's `y`, as `rw [← counterValue_eq, counterValue_bits]`;
  - the alternative route through `codeBitsNat_eq` (`rw [← foldr_bit_eq_ofDigits, ← codeBitsNat_eq]; exact codeBitsNat_bits t`).
- **No extra corollary is needed.** A named `Nat.ofDigits 2 ((Nat.bits t).map Bool.toNat) = t`
  would only be a convenience. It would have three consumers: R's window, R's loop, and H1.
- **#122 is declarations-only for R's cited material.** Its only removed line in the TuringMachine
  tree is a corrected docstring (`vhostSilentCfg_eq`) (`out/pr122-removed-lines.txt`,
  `out/pr122-turingmachine.diff`). The maintainer reports that its lemmas elaborate. I did not
  re-run #122's modules.
- **FYI for B5a's region, not R's:** landed H1 code already relies on the defeq this escalation
  avoids. `CodeSimulator.lean:5103` passes `(counterValue_bits t)` directly to `ht`
  (`out/e1-counterValue-grep.txt`). After #122 it could cite `counterValue_eq` instead.

**Other gaps.**

- **G2 (route gap, not raised by the report or the brief). The represented start's two
  auxiliary tapes.** `StepBlock.Rep_iff` requires two exact tapes:
  - the table tape exactly `bufferTape (tableBitsK tr)`, head 0;
  - the summary tape exactly `summaryCells (outputSummary []) (unaryFin q₀)`. That is cells 0
    and 1 blank and the unary state from cell 2 (`summaryCells`, `bufferTape`).

  `exists_installCallTM` yields `Cfg.ofWords exit (stateWord k (f α))`, a word at offset 0. The
  replay canonizer yields `serializeK = pairEncode n.bits (unaryFin q₀ ++ tableBitsK tr)`
  (`serializeK_eq`). Evidence for all of this: `out/route-gaps-evidence.txt`.

  So the brief's "install `serializeK …`, then install the unary initial state" does not
  produce `Rep`. The header must be skipped, the unary state split off and placed at offset 2,
  and the table placed on its own tape. No public machine or contract does this split.
  `pairExtractTM false true` leaves `unaryFin q₀ ++ tableBitsK tr`, and nothing splits off the
  self-delimiting unary prefix.

  **U2-S plans exactly this redistribution privately** (`UniversalK.exists_selfStartupTMK`'s
  docstring, line 182, and `briefs/u2s-fill-startup.md:166`). It lists "any reusable
  redistribution lemma" as a promotion candidate. H1's sketch has the same gap
  (`CodeSimulator.lean:5167`). Under ground rule 7 (one proof per shared argument), R should not
  write a second copy. **Decision needed:**
  - (i) wait for U2-S's redistribution to be promoted to a public host, then cite it;
  - (ii) promote a shared "serialization → step-block seam layout" phase now, as an API or host
    PR consumed by U2-S, H1, R and UN;
  - (iii) authorize R's own leaf, built from the catalog rows' `_run_ofCfg` contracts (as U2-S
    does), and accept the later dedup.
- **G3 (probe).** The continuation's probe must add the 12 external draft citations and the 2
  verdict and ledger lemmas listed in (c), plus #122's `counterValue_eq`.
- **G4 (`Cfg.Halted`).** It is a reducible `abbrev`, with no `Cfg.halted_iff`-style lemma. The
  draft's use matches the gated host's (`StepBlockLoop.lean:333`). The continuation brief should
  state that reading `¬ Halted` as `state ≠ none` is allowed, or the API should publish a
  one-line iff.
- **G5 (brief wording).** The brief prescribes R1 `embedSilentTM`, which halts with its source,
  for the captured passes. A seam needs the live return anchor of R1′, `embedSilentRetTM`, which
  is what the draft uses and what U2-S's route prescribes. The continuation brief should name R1′.

## (e) Environment

**What failed** (`out/env-log-lines.txt`, `out/env-timeline.txt`):

1. `lean-unmodified.log:1`: `error: failed to locate application`. This is the addendum's
   condition.
2. The shim worked. `lean-shim.log:1` gives `Lean (version 4.25.0, … commit cdd38ac5…)`, the
   same commit as the local v4.25.0 (`out/local-lean-version.txt`). `runtime-probe.log:1` gives
   `Nat : Type`, a core-only probe that does not exercise Mathlib.
3. The first `lake exe cache get` left `cache-get.log` empty (0 bytes). `bootstrap.log` stops
   after `MODULE 1 …Build/Zone`. The report says both logs were moved while open during disk
   exhaustion.
4. The cache retry (`cache-retry.log`):
   - line 5: `✔ [11/19] Built Cache.IO (10s)`;
   - line 8: `failed to read file '…/177f06803258/…/Cache/IO.olean', invalid header`;
   - line 12: `build failed`.

   Lake wrote `Cache.IO`'s olean in this run, and it was unreadable immediately afterwards.
5. The checks ran in a **different tree** (`/workspace/scratch/45e6e7dccd1a/tcslib`), whose
   packages had no Mathlib or Batteries oleans:
   - `zone-retry.log:1`: `…/mathlib/…/Mathlib/Algebra/BigOperators/Group/Finset/Basic.olean … does not exist`;
   - `bootstrap-retry.log:2`: `…/batteries/…/Batteries/Tactic/Alias.olean … does not exist`.
6. `environment.log:3` reads `Root filesystem exhausted repeatedly`. `environment.log:4` reads
   `Shared cgroup memory current/max: 8589627392/8589934592` (99.996 %). TMPDIR, `TCSLIB_OLEANS`
   and a checkout copy had been moved to `/dev/shm`.
7. `bootstrap-union.log` shows `PASS 1 …Zone`, then `MODULE 2 …ChoiceWords`. The run stalled and
   was terminated.
8. The final checks ran under self-imposed 20- and 60-second limits. `owned.log` and
   `import-probe.log` report missing `NDCodes.olean`, `axioms.log` reports missing
   `NDCodeSimulator.olean`, and `final-sweep.log:3` reads `FINAL_SWEEP_EXIT=124`.

**Root cause.**
- **Disk.** The root filesystem was too small for the Mathlib cache. At this pin Mathlib's build
  is **5,399,632 KiB ≈ 5.15 GiB** (`lib/lean` alone is 4,909,728 KiB). All packages together are
  5,751,596 KiB ≈ 5.5 GiB, before the downloaded `.ltar` archives. The 80 TCSlib modules add 235 MB of oleans
  (`out/env-sizes.txt`). The disk filled during the first cache get, which truncated output (the
  empty logs). In the retry, a freshly written `Cache/IO.olean` came out invalid.
- **Memory (secondary).** Moving storage into `/dev/shm` made it worse: tmpfs is charged to the
  8 GiB memory cgroup, which reached its cap. That is the likely cause of the union run's stall.
- **Two trees (tertiary).** The cache retry, toolchain and package builds lived in another
  scratch tree (`177f06803258`, 21 path mentions). The checks used `45e6e7dccd1a`
  (`out/env-timeline.txt`). So even a successful cache get could not have fed
  `lean_check_tree.sh`, which reads only `$ROOT/.lake/packages`.
- **Time.** The whole session spans 12:58 to 13:25 (file timestamps). The order list is 80
  modules and 94,672 lines (largest: `Build/Catalog` at 13,241 lines;
  `out/env-sizes.txt`), so the bootstrap could not finish in that window in any case.

**Proposed addendum changes (v2).**
1. **Storage and memory preflight, before `lake exe cache get`:**
   - record `df -Pk .` for the checkout, `df -T` or `stat -f` for every directory used, and the
     cgroup's `memory.max`;
   - require at least **8 GiB free** on the checkout's filesystem (Mathlib ≈ 5.15 GiB, all packages
     ≈ 5.5 GiB, plus archives, TCSlib oleans and temp);
   - if the check fails, stop and deliver an environment report. Measured sizes: `out/env-sizes.txt`.
2. **No tmpfs.** Never put `.lake`, the Mathlib cache, `TCSLIB_OLEANS` or `TMPDIR` on `/dev/shm`
   or any tmpfs: it counts against the memory limit (`environment.log:4`).
3. **One checkout.** Run the cache get, the bootstrap and every check in the same clone.
   - Never reuse another session's scratch tree, package builds, toolchain or object store, and
     never union `LEAN_PATH`s across trees.
   - If the toolchain is not under elan, record its path and `lean --version`. The commit must be
     `cdd38ac5…`.
4. **Cache verification before the bootstrap.**
   - `lake exe cache get` exits 0.
   - `find .lake/packages -name '*.olean' -size 0` is empty.
   - Spot-check the two oleans the failed runs named: `Mathlib/Algebra/BigOperators/Group/Finset/Basic.olean`
     and `Batteries/Tactic/Alias.olean`.
   - Make the runtime probe import Mathlib (e.g. `import Mathlib.Algebra.BigOperators.Group.Finset.Basic`)
     through `lean_check_tree.sh`. A `Nat`-only probe does not test the cache.
5. **One retry, then stop.** After an interrupted or failed cache get, free space and remove
   zero-size or truncated outputs: `Cache/` oleans and IR under `mathlib/.lake/build`, and
   anything the `find` above lists. Retry once. If it fails again, stop. No sparse checkouts,
   alternates or other workarounds.
6. **Logs.** `tee` every log to its final path from the start. Never move a log that a running
   process is writing.
7. **No checks against missing prerequisites.** If the bootstrap fails, record its tail and skip
   the checks that need its products. Do not run self-timed final checks: they only add FAIL
   noise.
8. **Optional (user decision).** Attach a maintainer olean snapshot of the base's 80 modules
   (≈ 235 MB uncompressed, with its SHA-256), so a worker can skip the 94,672-line bootstrap. The
   maintainer's replay stays authoritative. This would change current practice ("no TCSlib
   olean from another fill").

The shim part of the addendum worked as written. No change is needed there, beyond allowing a
non-elan `LEAN_SYSROOT` in item 3.

## (f) Recommendation

**Landing: do not land (default confirmed).**
- The delivery adds no proof.
- The imports elaborate cleanly and leave the replay set unchanged, but they are trivially
  re-added as the continuation's first edit (region (a)).
- The appendix records this sandbox's failure and E1, which goes stale once #122 merges.
- A PR and audit gate for zero proof progress costs more than it gives.

Carry the following into the cont1 brief instead:
- the two imports;
- the four drafts;
- the conditional ledger.

**C1-R cont1 brief:**
1. **Pin** at a campaign commit that contains #122 (`counterValue_eq`, `codeBitsNat_eq`), with a
   fresh olean snapshot. **Cont1 must wait for #122 to merge.** Rule 10 forbids reading
   `counterValue` without its equation, and both phase 2 (the window copier's `y`) and phase 3
   (the loop's `ht`) need it. Phase 1 alone does not, but a split pin is not worth it. Pinning at
   #122's unmerged head (`b6627401`) instead would be a user decision; it is not the campaign's
   practice.
2. **Keep, verbatim** (from `probes/DraftProbe1.lean.drafts.txt`, verified here against
   `oleans-lndnf`), and re-elaborate them at the new pin: `ic_header_result`,
   `ic_capture_return` and `ic_replay_window`, as pre-verified region-(b) privates.
   - Keep `ic_table_call` only as a pattern. It changes with the G2 decision.
   - Also keep the conditional ledger and the constant `C = a + b + w + 50(L + 1) + 10`.
3. **Route changes:**
   - (a) Captured passes use **R1′ `embedSilentRetTM`** with fresh banks, through
     `ic_capture_return` (G5).
   - (b) E1: `ht := (counterValue_eq _).symm.trans (counterValue_bits t)`, and the window's `y`
     the same way.
   - (c) Decide **G2** first and name the mechanism in the route (shared with U2-S, H1 and UN).
   - (d) State the `Cfg.Halted` reading (G4).
   - (e) The window needs `(pairEncode u x).drop (2|u| + 2) = x`, from `pairEncode_eq` and the
     length lemmas.
4. **Probe:** the base's 77 names plus the 12 external draft citations and 2 verdict/ledger
   lemmas listed in (c), plus `counterValue_eq`.
5. **Environment:** issue with addendum v2 (e).
6. **Promotion candidates to track:** the two-pass header split (`ic_header_result`; UN and
   B5a's H1 need it), the first-halt R1′ capture (`ic_capture_return`; three inline uses exist),
   and the G2 redistribution.

**Decisions needed (user):**
- G2's mechanism: (i) wait for U2-S's promotion, (ii) promote a shared host now, or (iii) R's own
  leaf.
- The optional olean snapshot in addendum item 8.

Review artifacts to clean up later:
- the worktree `wt/` (`git worktree remove`);
- the ref `refs/review/c1-core`.
