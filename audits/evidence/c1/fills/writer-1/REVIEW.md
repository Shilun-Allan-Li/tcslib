# Review: C1-W fill delivery (the bounded choice writer, `Turing.ndWriterTM_run_block`)

Read-only review by the maintainer's review sub-agent, 2026-10-17. Every claim below cites a
saved command output under this directory (`out/NN-*`). The delivery is treated as data.

**Verdict.** Integrity and scope pass. The delivery is a docstring-only partial, and the target
is still `sorry`. The worker's unelaborated draft **does not compile as delivered** (3 errors).
**Four one-line repairs make it a complete proof**: zero errors, zero warnings, and clean axioms
for the target and all seven assembly theorems. The environment failure was a dependency
bootstrap that destroyed itself, through disk exhaustion and a Lake re-clone. It was not Lean.

**Not clear to merge: nothing in this delivery should land.** The only change is the
docstring appendix. Following the default for partials blocked by the environment, its content
goes into the C1-W cont1 brief instead (see (f)).

## Inputs

| Input | Identity | Evidence |
| --- | --- | --- |
| Delivery zip `infra_local/fill-c1-writer.zip` | SHA-256 `8fe2cfbf…a507a932`, 18 files | out/02, out/04 |
| Extracted delivery `$S/incoming/c1-writer/` | SHA256SUMS: 17 of 17 OK | out/01 |
| Brief (dispatch copy) | SHA-256 `21d13911…ea89051`, matching the issued hash | out/02 |
| Brief (repo copy, `$S/wt-hk/briefs/c1-fill-writer.md`) | differs only by the `@ANCESTOR@` placeholder | out/03 |
| Environment addendum | SHA-256 `a25474c5…f8d2928`, matching | out/02 |
| Base `83ec6348b325f060cec2a917b45a4eda6e301d84` | Lean tree equals `6d18902f` (empty Lean diffstat) | out/05 |
| Olean snapshot | `$S/oleans-lndnf` | — |

Review worktrees: all detached, all under this directory, each with the Mathlib link.

- `wt` is the base.
- `wt-head` is the delivered head `e0cc4835`.
- `wt-draft` is the head with the repaired draft v2 installed, uncommitted.
- `wt-draft4` is the head with the merged-step variant v4 installed, uncommitted.

The bundle head was fetched into `refs/review/c1-writer`. No branch or working tree of the main
repository was touched. The review's scripts are in `scripts/` and its probe files in `probe/`
(hashes in out/42).

## (a) Integrity and scope

| Check | Result | Evidence |
| --- | --- | --- |
| `git bundle verify` at the base | OK. One ref, `refs/heads/fill/c1-writer` = `e0cc4835bf99445fb00d42ed48eb19f8bae2a00d`. Its only prerequisite is the base. | out/06 |
| Head hash vs REPORT.md | identical (`e0cc4835…`) | out/06 |
| Parent | exactly `83ec6348…`, one commit (author "Codex") | out/06 |
| Head blob vs delivered `NDHost.lean` | byte-identical (SHA-256 `908dc100…`) | out/08 |
| Patch | applies cleanly to the base blob and reproduces the delivered file byte for byte. Its hunks equal `git format-patch` of the head. | out/08, out/09 |
| `git diff --check` | clean | out/09 |
| Files changed | one, `Build/NDHost.lean`, +9/−1 in a single hunk inside the target's docstring | out/07 |
| Appendix removal | removing delivered lines 200–207 and re-attaching ` -/` to line 199 restores the base byte for byte | out/35 |
| Declarations | 25 public / 2 private at both base and head, so none new. 1,098 → 1,106 lines. | out/22-lint-wt.txt, out/22-lint-wt-head.txt |
| Admission | the `sorry` and the literal **Proof sketch** are unchanged. No new axiom or admission. | out/07, out/35, out/36 |
| Line widths | added lines are at most 92 characters. The file's three lines over 100 (797, 803, 1048) are the base's 789, 795, 1040 shifted by 8. | out/09 |
| Rule 11 | the added lines contain no R3 row and no private name from another file | out/43 |
| Screens | the delivered before/after files are byte-identical to the repo's screen base (`2374e369…`) | out/17 |
| Quoted base sorry set | equals `audits/logs/c1-fill-writer-base-sorries.txt` (35 entries in 15 modules) | out/44 |
| Observed tip `2cce4804` | a real commit that has the base as an ancestor | out/38 |

**Accuracy of the appendix.** It is accurate and does not overclaim. It calls the draft
"unverified" and says the admission remains. It is still not landable content, for three reasons:

- it points to `REPORT.md`, a delivery file that is not in the repository;
- it narrates the sandbox environment inside a mathematical docstring;
- its first sentence ("leaves the contract open") becomes false the moment the proof lands.

## (b) Elaboration

All elaborations ran through `leanelab.sh` against `oleans-lndnf`, one at a time.

| File | Result | Evidence |
| --- | --- | --- |
| Base `NDHost.lean` | exit 0; one warning, `200:8 declaration uses 'sorry'` (the target) | out/10 |
| Head `NDHost.lean` | exit 0; one warning, `208:8 declaration uses 'sorry'` (the same declaration, 8 lines lower). No error, no other warning. | out/11 |
| Head plus `#print axioms` | the target and the 7 assembly theorems carry `sorryAx`; `guessRunTM_runWith_setup_halt` and `guessRunCfg_clean` are clean. This matches REPORT.md's source-level walk. | out/36 |
| Import probe (the brief's 20 `#check`s verbatim, plus 34 further names cited by the draft) | exit 0, no errors or warnings | out/20 |

The sorry count is 1 at both base and head. The import probe imports the base `NDHost.olean`.
That is equivalent for this purpose, because the head differs from the base only in a docstring.

## (c) The draft

**Extraction.** `scripts/build_probe.py` takes the two `lean` blocks verbatim from REPORT.md
(lines 197–337, the helpers; lines 345–359, the body). It inserts the helpers at region (a),
after line 187, replaces the `sorry` (line 224) with the body, and appends axiom prints. The
result is `probe/C1WriterDraftProbe.lean` (out/12).

**As delivered: it does not compile.** There are 3 errors and 6 unused-simp-argument warnings
(out/13). The probe's line numbers are cited.

1. **`wr_cfg_step`, state field (261:2), "unsolved goals".** `rw [Action.apply_state]` leaves
   `{…}.state = (wr_cfg j c (s ++ [b])).state`. The closing `rfl` of `rw` runs at reducible
   transparency and cannot unfold the private def `wr_cfg`. **Repair:** add `rfl` on its own
   line.
2. **`wr_cfg_step`, head field (278:6), `omega` fails.** The leftover atom is
   `(if True then (some (some b), 1) else (none, 0)).2`. After `subst i`, the simp argument
   `if_pos rfl` is reported unused, so the `if` is never reduced and `SignType.coe_one` cannot
   fire. **Repair:** replace `if_pos rfl` with `↓reduceIte`. Make the same change in the
   tape-field bullet (268), where the same unused `if_pos rfl` was silently rescued by the
   definitional check of `exact`.
3. **Target body, second clause (376:2), "unsolved goals".** The goal
   `some (run ()) ≠ some done` remains, because `reduceCtorEq` needs the `some` constructors
   peeled first. **Repair:** use `simp only [wr_cfg, ne_eq, Option.some.injEq, reduceCtorEq,
   not_false_eq_true]`.

Everything else elaborated as written: `wr_cfg`, `wr_tape_append`, `wr_cfg_nil`, `wr_cfg_scan`,
`wr_cfg_finish`, `wr_prefix`, and the body's first clause.

**Repaired draft (v2): a complete proof.** The four edits, applied with asserted replacements,
are in out/14. The probe exits 0 with no errors or warnings (out/15). The target and all seven
assembly theorems print `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.
Installed at the real path in `wt-draft`, `NDHost.lean` elaborates with exit 0 and no output,
so there is no sorry warning (out/18). The installed diff is out/40.

**Remaining work: no mathematical work.** Four edited lines, then the verification
bookkeeping: the sweep, the screens and the report.

**Route.** The draft follows the brief's route exactly:

- the written-prefix configuration `wr_cfg`: state `run ()`, the block updated by
  `FinTM.bufferTape s`, the head at `+|s|`, every other field `c`'s;
- one induction on the prefix length (`wr_prefix`, with `u ≤ m` and `u ≤ |w|`);
- `wr_cfg_scan` for the unwritten next cell;
- write-and-move at a nonblank cell (`wr_cfg_step`, through `wr_tape_append` and
  `FinTM.bufferTape_append`);
- the stationary live exit at the blank (`wr_cfg_finish`);
- the split `w = w.take m ++ [w[m]]` with `runWith_append`;
- the second clause from the same invariant at `u = |w'| ≤ m`.

`m = 0` needs no separate case. The gate's instance tests (`m = 0`, `m = 2`, and the necessity
of `hblock`) follow from the unchanged statement.

**Rule 10.** The draft reads every step through `NDTM.stepWith_of_some`, with `(by rfl)` on
the private def's state. It reads every action through `Action.apply_state`, `_inputPos`,
`_workTapePos`, `_output` and `Action.apply_workTapes`. It never unfolds `NDTM.stepWith`,
`NDTM.runWith` or `Action.apply`. The only definitions it unfolds are `ndWriterTM` (its own
file's) and its own private `wr_cfg`.

- **The two unrestricted `simp` calls** (both in `wr_cfg_nil`) use only `wr_cfg`,
  `List.length_nil`, `Nat.cast_zero`, `add_zero`, `FinTM.bufferTape_nil`, `Function.update_*`,
  `↓reduceIte`, `ne_eq` and `not_false_eq_true` (`simp?` output, out/21).
- **`exact wr_tape_append …`** closes at reducible transparency. The two
  `exact moveInputPos_zero _` steps need default transparency, but only to unfold the private
  `wr_cfg` and to project out of an explicit structure value (out/37).
- **Names cited beyond the probe list** are `Turing.Cfg.ext` and `Turing.moveInputPos_zero`,
  both public in `Configuration.lean`, plus core and Mathlib names. All of them resolve in the
  expanded probe (out/20).

**Rule 11.** The draft cites no R3 row and no private declaration of another file (out/43).
There is one name coincidence. The draft's `wr_prefix` has the same short name as a private
`wr_prefix` in `Build/WindowRun.lean`, whose B6 brief also assigned the `wr_` prefix. Lean
keeps private names apart per module, so this is harmless, but a rename keeps the
private-name record unambiguous. The other token hits ("empty", "one", "test") are English
words in docstrings.

**Lint and widths (v2).** 0 FAIL, 30 WARN over 37 files, the same as the base. `NDHost` has
1,263 lines, 25 public / 9 private declarations (out/22-lint-wt-draft.txt). No new line exceeds
100 characters (out/19).

**Duplication (v2): one pair at the 90% copy threshold.** The v3 screen over the brief's
7-file population was run once, under `nice -n 10` (out/23, out/24).

| | Declarations | Pairs | Characters |
| --- | --- | --- | --- |
| Base | 780 | 1,018 | 380,649 |
| v2 installed | 788 | 1,021 | 381,349 |

There are no new cross-file pairs. Three new pairs are within the file:

- **`wr_cfg_step` reproduces `wr_cfg_finish` at 430/474 = 91%.** The two share the
  `stepWith_of_some` / `Cfg.ext` / five-field skeleton. This is at or above the brief's 90%
  "copy" line. Under `policy.md` **Duplication** it would need disclosure and human approval.
- **`guessRunCfg` reproduces `wr_cfg` (56%), and `wr_cfg` reproduces `guessRunCfg` (50%).**
  Both are the block-update expression that the frozen target statement and `guessRunCfg`
  prescribe. `guessRunCfg` is defined after the target and keeps the head fixed, so region (a)
  cannot reuse it. One line of justification each is enough.

**Merged-step variant v4 (the review's probe, not the worker's): clears the 91% pair.** It
replaces `wr_cfg_step` and `wr_cfg_finish` with a single `wr_cfg_stepWith`, whose right side is
`if c.workTapes j (c.workTapePos j + s.length) = none then { wr_cfg j c s with state := some
.done } else wr_cfg j c (s ++ [b])`. It shares the state, input-head and output fields through
`split_ifs <;> apply Cfg.ext <;> first …`, and carries a literal Proof sketch. The diff from v2
is out/39 and the installed diff is out/41.

| Check (v4) | Result | Evidence |
| --- | --- | --- |
| Probe elaboration | clean; clean axioms for all 8 | out/25 |
| Installed elaboration | exit 0, no output | out/26 |
| Lint | 0 FAIL; 1,245 lines; 25 public / 8 private | out/27 |
| Widths | no new line over 100 characters | out/28 |
| Screen | 787 declarations / 1,020 pairs / 380,919 characters. The only new pairs are the two statement-shaped `wr_cfg`/`guessRunCfg` pairs (56% and 50%). | out/29, out/30 |

**Disclosure.** The v4 screen ran at the same time as another reviewer's small 3-file screen
(out/45). The results are unaffected, but the one-screen-at-a-time rule was not met for
part of that run. The v2 screen ran alone.

## (d) Environment

**What failed, in the worker's logs:**

1. **Startup.** The unmodified Lean failed with `error: failed to locate application`, so the
   addendum's condition held. The shim's SHA-256 `985924ad…` matches the addendum and the
   shipped `evidence/runtime/executable-path.c` (not compiled or run here). With it, Lean
   printed `Lean (version 4.25.0, x86_64-unknown-linux-gnu, commit cdd38ac5…)`. Core-only
   probes passed, also single-threaded (`logs/bootstrap.log`, `logs/runtime.log`).
2. **No Mathlib build.** The first bootstrap failed with `Build/Zone.lean:6:0: error: unknown
   module prefix 'Mathlib'`. The search path lists seven package build directories but no
   `mathlib/.lake/build/lib/lean`: the checkout had no Mathlib build at all
   (`bootstrap-setup-failure` in `logs/bootstrap.log`).
3. **Lake re-clone.** `lake exe cache get <35 Mathlib modules>` printed
   `PFR: URL has changed; deleting '…/packages/PFR' and cloning again`, then the same for
   mathlib (`cloning https://github.com/leanprover-community/mathlib4.git`). Lake judged the
   provisioned packages' remote URLs to differ from `lake-manifest.json`, and deleted and
   re-cloned them. The retries produced no output; "interrupted attempts returned 130"
   (`cache.log`, `cache-retry.log`).
4. **Disk exhaustion.** "A dependency-copy attempt exhausted disk space. Empty cached oleans
   were detected." The next bootstrap died with `Segmentation fault lean "$rel.lean" -o …`,
   `lean exited with status 139` at `Build/Zone`. "At 20:11 UTC the filesystem reported 0
   available bytes", and REPORT.md adds an index-write failure (`bootstrap-corrupt-cache`).
5. **Modified checkout.** `cache-verified.log` shows `warning: mathlib: repository … has local
   changes`.
6. **Recovery attempts.** The worker reused another scratch directory's packages read-only
   through `LEAN_PATH` (`/workspace/scratch/8032237c75d4/…`; all 11 pins MATCH in
   `dependency-pins.log`) with `lean -j 1`. The Mathlib import probe left an empty log and was
   interrupted (130). Further bootstraps were interrupted (130) at `Build/Zone` "under resource
   pressure".
7. **Final checks.** The sweep, under the worker's own 60-second bound, ended `EXIT_STATUS=124`
   at its first module (`logs/final-sweep.log`). The owned-file check failed with
   `object file …/Build/Seam.olean … does not exist` (exit 1, `logs/owned-file.log`). The
   import and axiom probes failed with `…/Build/NDHost.olean … does not exist` (exit 1).

**Diagnosis.** The logs record no `df` output and no durations. The order of events, and the
cause of the final stall, are therefore partly inferred.

- **Primary cause: the bootstrap destroyed itself.** The sandbox's checkout had no Mathlib
  build, and both ways the worker tried to get one damaged the environment:
  - Copying a dependency tree filled the disk. That left zero-length or truncated `.olean`
    files, and Lean crashes on importing a truncated olean instead of reporting an error (the
    exit 139).
  - `lake exe cache get` resolves the whole workspace first. Because the package URLs did not
    match the manifest, it deleted mathlib and PFR and started full git clones. PFR is a
    `require` in `lakefile.lean`, yet no module of the order list imports PFR or LeanAPAP
    (out/16).
- **Secondary cause: caps too short, and the wrong module first.** The worker's own time caps
  (60 seconds for the sweep; interrupts with exit 130) were too short for a cold start on a
  degraded host. The order list also begins with `Build/Zone`, which is not even upstream of
  `NDHost` (out/32).

**Measured requirements** (on this machine):

| Item | Measurement | Evidence |
| --- | --- | --- |
| Dependencies of the 80-module order list | 715 Mathlib modules (plus batteries, aesop, Qq and others), ≈572 MiB of build artifacts, of which ≈549 MiB are `.olean` | out/16 |
| Dependencies of NDHost's own stage (NDHost and its 17 upstream TCSlib modules) | 609 Mathlib modules, ≈496 MiB | out/34 |
| Full Mathlib build, for comparison | 4.7 GiB, plus 497 MiB of `.git` and 1.1 GiB of `~/.cache/mathlib` | out/16 |
| Who imports NDHost | only the umbrella `TCSlib/Complexity/TuringMachine`; 61 of the 80 modules are neither upstream nor downstream of NDHost | out/32 |
| Elaboration time (`-j4`, warm page cache: a lower bound for the worker's host) | `Build/Zone` 2 s; `NDHost` 2–7 s | out/31, out/10, out/11 |

**Proposed changes to the environment addendum** (for C1-W cont1, and for fills generally):

1. **Disk preflight.** Before any Lean or Lake command, record `df -Pk` for the checkout,
   `$HOME/.cache` and the scratch directory, both in REPORT.md and in a log. Require at least
   3 GiB free for the selective route, and at least 8 GiB before any full
   `lake exe cache get` or re-clone. If space is short, stop and report. Repeat the check after
   each cache step.
2. **Package preflight.** For every package, compare `git -C .lake/packages/<p> remote get-url
   origin` and `git -C .lake/packages/<p> rev-parse HEAD` with `lake-manifest.json`. If any URL
   differs, run no Lake command that resolves the workspace: `lake exe cache get` would delete
   and re-clone (`cache.log`). If Lake prints `URL has changed; deleting`, interrupt at once and
   stop. One option, which needs the user's authorization: allow `git remote set-url` to the
   manifest URL when the pinned revision already matches.
3. **No copies.** Never copy a dependency tree. Reference an existing build read-only, through
   `LEAN_PATH` or a symlinked `.lake/packages`, as our own replay worktrees do.
4. **Olean integrity.** Before the bootstrap:
   - `find <each LEAN_PATH entry> -name '*.olean' -size 0` must print nothing (a zero-length
     olean crashes Lean with exit 139);
   - a one-file probe importing the order list's direct Mathlib imports must exit 0.
5. **Staged bootstrap.** Ship a stage-1 list: `out/33-stage1-order.txt`, the 17 upstream
   modules of NDHost plus NDHost, in dependency order. Run it first, then the owned-file check,
   the import probe and the axiom probe. Run stage 2 (the other 62 modules, of which only the
   umbrella depends on NDHost) afterwards. A partial that completes stage 1 is verifiable.
6. **Time budget.** No short caps. Run the sweep in the background with timestamps per module.
   Give the reference timings above. Declare a hang only after, for example, 10 minutes without
   progress on one module, and then log `uptime`, `free -m` and `df`.
7. **Stop rule.** After one failed attempt at each route (cache retrieval, read-only reuse),
   stop. Deliver the draft as text with the `df` and timing evidence. No recovery loops; this
   worker made about six attempts.
8. **Optional fallback.** Mathlib's cache files are the same on every platform. If the sandbox
   cannot download, the maintainer could provide a tarball of just the ≈0.5 GiB dependency
   closure, made from the stage list.

## (e) Other escalations

- **No API gap: confirmed at the base.** REPORT.md raises none ("No missing public lemma was
  established"). The repaired draft proves the target from the brief's API, plus the public
  `Cfg.ext` and `moveInputPos_zero` and core and Mathlib names (out/15, out/20). No equation
  needs to be drafted.
- **Promotion candidate: a note only.** The generic written-prefix invariant (`wr_cfg` plus
  `wr_prefix`) is a fair candidate for the controller-stopped writer. A related observation:
  `Build/Seam` has a private `seam_stationary_apply` (a stationary, silent, write-free action
  changes only the state), proved with `simp [Action.apply]`. A public version would serve the
  writer's exit step and the hosts' dispatch steps. That belongs to the dedup queue, not to
  this brief.
- **REPORT.md's other claims: confirmed on spot checks.** The line and declaration counts, the
  lint line, the hashes, the ancestor check and the R3 and private-name greps all hold (out/06,
  out/22, out/43). The worker counted 4,917 private names in other files; the broader pattern
  used here counts 5,091. Neither finds a hit in the delivery.
- **The `wr_` prefix and `wr_prefix` coincide with `Build/WindowRun.lean`.** This is
  low-severity (see (c), Rule 11).

## (f) Recommendation

**Land nothing from this delivery: the default is confirmed.** The appendix is accurate, but
it points to an out-of-tree `REPORT.md`, narrates the environment, and goes stale the moment
cont1 lands. Carry its facts into the cont1 brief. Cont1 branches from the same base, so the
appendix will not be present in it.

**The C1-W cont1 brief should:**

1. **Keep the setup.** Same base `83ec6348…`, the same regions (a)–(c), the same frozen target,
   and ground rules 1–11 unchanged. Region (c) may stay empty: the maintainer updates the
   status text at integration.
2. **Carry the draft and the review's results.** Include:
   - the worker's two blocks from REPORT.md;
   - this review's three error messages;
   - the four repairs (out/14), verified here: zero errors, no warnings, no sorry, and clean
     axioms for the target and the seven assembly theorems.
3. **Settle the 91% pair.** Require one step lemma in place of `wr_cfg_step` and
   `wr_cfg_finish` (the verified v4 shape, out/39), or else a disclosure of the 91% pair for
   human approval. Require one line of justification for each `wr_cfg`/`guessRunCfg` pair:
   the shape is prescribed by the frozen statement, and `guessRunCfg` comes after the target.
4. **Optionally, rename `wr_prefix`**, for example to `wr_run_prefix`, to avoid WindowRun's
   private short name. Keep the `wr_` prefix.
5. **Ship the expanded import probe**: the 20 names of the brief plus `Turing.Cfg.ext`,
   `Turing.moveInputPos_zero` and the core and Mathlib names (`probe/C1WriterImportProbeExpanded.lean`).
6. **Attach the revised environment addendum**: items 1–8 of (d), with the stage-1 order list.

**Alternative for the user.** The repaired draft elaborates against the base snapshot in
seconds, with clean axioms, and v4 also screens clean apart from the two statement-shaped
pairs. The user could therefore send the verified draft, credited to the worker, through the
normal PR and audit-gate route, instead of spending another fill round on the environment.
That departs from the fill-by-worker workflow, so it is the user's decision.
