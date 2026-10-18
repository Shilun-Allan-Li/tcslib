# Review: C1-WC fill delivery, the input window copier (`Turing.exists_inputWindowCopyTM`)

Read-only review for the maintainer, 2026-10-17. Paths below are relative to
`$S/review/c1-window-fill/` unless absolute. `out/NN-*.txt` are the saved command outputs.

**Not clear to land.** The delivery is a docstring-only, environment-blocked partial. Its appendix
also names an exit-join route (`Turing.phaseHostTM_run`) that cannot be reached from
`Build/InputWindow`'s import context. The plan is carried into C1-WC cont1, with the corrections
in (f).

## Inputs

| Item | Value | Evidence |
|---|---|---|
| Delivery zip | `infra_local/fill-c1-window.zip`, SHA-256 `555c23f0…` (11 members) | `out/01` |
| Extracted copy | `$S/incoming/c1-window/`; every member is byte-identical to the zip | `out/02` |
| Brief (dispatch copy) | `infra_local/fill-dispatches/c1-fill-window.md`, SHA-256 `4c05c6af…` (matches) | `out/01` |
| Brief (repo copy, `wt-hk`) | differs from the dispatch copy only by the 3 `@ANCESTOR@` substitutions | `out/02` |
| Addendum | `fill-environment-addendum.md`, SHA-256 `a25474c5…` (matches) | `out/01` |
| Base | `83ec6348b325f060cec2a917b45a4eda6e301d84`. Its Lean is identical to `75edca6f` and `6d18902f` | `out/07` |
| Head | `555f7f253828af2cb097401e094765e42ac47edf` (author "Codex") | `out/04` |
| Olean snapshot | `$S/oleans-lndnf` | `out/08`, `out/09` |
| Review worktree | `wt/`, detached. Built at the base, then switched to `refs/review/c1-window` (the head); the Mathlib link is in place | `out/03`, `out/09` |

## (a) Integrity and scope

Integrity: everything checks out.
- `shasum -c SHA256SUMS`: all 10 listed files OK. `SHA256SUMS` itself is the only unlisted file
  (`out/01`).
- `git bundle verify` at the base: okay. The one prerequisite is exactly the base. The one head is
  `555f7f25… refs/heads/fill/c1-window` (`out/03`).
- I fetched it to `refs/review/c1-window`. The single parent is the base, and `base..head` is one
  commit. The head hash matches REPORT.md (`out/04`).
- Patch, bundle and file agree. The patch applies cleanly to the base. Applying it gives blob
  SHA-256 `407e5cef…`. That equals the head's blob and the delivered file (`out/04`).
- The shim source `evidence/runtime/executable-path.c` has SHA-256 `985924ad…`, the addendum's
  hash. I did not compile or run it.

Scope: verified as the report describes.
- The diff is one file, `Build/InputWindow.lean`, +8/−1 (`out/04`, `out/05`).
- The only change is the docstring's last line. The ` -/` closer moves onto its own line, as the
  brief requires, and the flagged **Fill appendix (C1-WC)** paragraph is added before it.
- The header, imports, module docstring, statement, `sorry` body and file tail are byte-identical
  to the base (`out/05`).
- There are no new declarations, axioms or admissions. The only `sorry` is the original one at
  line 89 (`out/05`).
- Added lines are at most 90 characters, and the whole file at most 97. `git diff --check` is
  clean. The file grows from 84 to 91 lines (`out/05`).

Accuracy of the appendix. It has two problems, and nothing in it is false about the proof's
status.
1. **Wrong route (substantive).** The appendix says the planned one-step exit join "uses the public
   `Turing.phaseHostTM_run`". That lemma is public, but it lives in `Build/Seam`, which is not in
   `Build/InputWindow`'s import closure.
   - The static closure has 21 TCSlib modules and no `Build.Seam` (`out/06`).
   - Elaborating `#check @Turing.phaseHostTM_run` and `#check @Turing.phaseHostTM` from
     InputWindow's imports gives `Unknown identifier` for both (`out/11`). With
     `import …Build.Seam` both resolve (`out/11b`).
   - The route therefore needs an import, and ground rule 6 forbids adding one. REPORT.md
     proposes extending the probe with exactly this `#check`; that extension would fail.
2. **Session narrative in a library docstring (minor).** "the required bootstrap crashed after the
   prescribed runtime fallback, so no new Lean proof has been validated in this continuation" is
   a run record, not library text. It is also inexact: C1-WC's first round is not a continuation.

The C = 6 claim in the appendix is arithmetically right; see (c).

## (b) Elaboration

All elaborations used `tools/leanelab.sh <wt> $S/oleans-lndnf <file>`, one at a time.

| Run | Result | Evidence |
|---|---|---|
| `Build/InputWindow.lean` at the base | exit 0; 1 warning, `59:8 declaration uses 'sorry'`; 0 errors | `out/08` |
| `Build/InputWindow.lean` at the head (file SHA `407e5cef…`) | exit 0; 1 warning, `66:8 declaration uses 'sorry'` (the same target, shifted 7 lines); 0 errors | `out/09` |
| Issued 49-check import probe (copy byte-identical to the base's `.lean.txt`; unchanged base..head) | exit 0; 0 errors, 0 warnings; 49 of 49 `#check`s print | `out/10` |
| Style lint at the head | `0 FAIL, 30 WARN over 37 files`, the base's line; InputWindow at 91 lines, 1 public / 0 private | `out/18` |
| Copy-text screen v3 at the head (one run, `nice -n 10`) | 125 declarations, 43 pairs, 11,684 chars; byte-identical to the base screen and to the delivered `screen-after.txt`; no InputWindow pair | `out/17` |
| REPORT's base sorry list (35 entries in 15 modules) | identical to `audits/logs/c1-fill-window-base-sorries.txt` | `out/19` |

The sorry count is 1 at the base and 1 at the head; nothing was added or removed.

I did not run the 80-module downstream sweep. The change is comment-only and adds no import, so no
downstream elaboration can change. REPORT.md likewise only expects the warning set to be
unchanged; it did not observe it.

## (c) Draft / plan

REPORT.md contains **no Lean proof text**. It describes scratch drafts that never elaborated and
excludes them. What it offers is a plan, which I assessed against the brief and the base's API. I
probed its two load-bearing new elements.

**The plan matches the brief's route and is sound, except for the exit join.**
- **Body.** It is a one-tape `Bool`-state leaf. The anchor is `false` and the escape is `true`. On
  `some b` it writes `b`, moves both heads right and returns to `false`. On `none` it takes one
  stationary silent step to `true`.
  - This is the brief's body. It also reads `counterLoopTM`'s actual type correctly:
    `MultiTapeTM k → MultiTapeTM (k+1)`, with the counter at `Fin.last k`.
  - The brief's phrase "a two-tape body: tape 0 is dst, tape 1 is the counter" is loose. The body
    is one-tape; the loop is two-tape. cont1 should say so.
- **Rounds.** Exhaustion uses `counterLoopTM_run_done` with `τ = 1` and `|y| = d` rounds.
  - The early end uses `counterLoopTM_run_escape` at `r₀ = |y| < d`: rounds `0..|y|−1` return,
    round `|y|` escapes, and `e = true ≠ a = false`.
  - Those statements' hypotheses and endpoints fit. The all-`true` counter on exhaustion, and
    `counterWord w (|y|+1)` with `counterWord_length` on escape, give the statement's `w'`.
  - The four edge cases of the brief fall under these two cases: `d = 0` is exhaustion with one
    underflow; `p = |z|` with `d ≥ 1` escapes at `r₀ = 0`.
- **Embedding.** The plan selects `dst` and `j` with R1 (`embedEmitTM`, `ι : Fin 2 ↪ Fin k`, with
  `0 ↦ dst` and `1 ↦ j`). It decomposes the start configuration by `embedEmitCfg_eq` and the
  counter layout by `counter_cfg_eq`. The endpoint fields come from `embedEmitTM_runFrom`, `_frame`,
  `embedEmitCfg_selected_*`, `_unselected`, and the `simps` equations `embedEmitCfg_state`,
  `_inputPos`, `_output`. All resolve from the file's import context (`out/10`, `out/11`).
- **Exit join.** This is the defect. `phaseHostTM` / `phaseHostTM_run` are out of the import
  closure; see (a), item 1.
  - **There is a substitute inside the closure.** The probe `probes/IWReviewJoin.lean` (SHA-256
    `3bb58d12…`) elaborates with 0 errors and 0 warnings, within `[propext, Classical.choice,
    Quot.sound]` (`out/12`).
  - It defines `iwProbe_joinTM`: `counterLoopTM M a (some e)`'s table, except that `.escape` takes
    one stationary silent step to `.done`.
  - `iwProbe_join_prefix`: before `escape` is visited, the join's run equals the loop's run. It is
    one application of the public `MultiTapeTM.runFrom_eq_of_agreeOn` (`Simulation`), with
    `Q = {q | q ≠ .escape}`. The loop's own "no `escape` before T" clause discharges the guard.
  - `iwProbe_join_step`: from `escape`, one step reaches `done` with every other field unchanged.
    It uses `step_of_some`, `Action.apply_*`, `moveInputPos_zero` and `Cfg.workTapeSymbols_eq`,
    with no foreign definition unfolded.
  - Exhaustion therefore needs no join step. The escape case needs one. First arrival at `done`
    follows from the loops' `∀ t < T, state ≠ done ∧ ≠ escape` clauses.
  - Its only touch of another file's definition is introducing `MultiTapeTM.AgreeOn` by `intro`;
    see (e).
- **Ledger (verified).** `C = 6` holds in both cases (`out/12`). The bounds below use the probe's
  sum form with `τ = 1`.
  - `iwProbe_ledger_done` checks exhaustion with a join step:
    `d + overhead(d+1) + 1 ≤ 6(d+1) + 2|w|`, from `counterOverhead_le`.
  - `iwProbe_ledger_escape` checks the early end at `r = r₀+1`:
    `r + overhead(r) + 1 ≤ 6r + 2|w|`, from `counterOverhead_le_of_le`.
  - With the probe's join, exhaustion has no extra step and `C = 5` would do there
    (`iwProbe_ledger_done_nojoin`). The escape case still needs 6. So **`C = 6`** stands, as
    REPORT.md planned.
- **Promotion candidate.** A generic "counter loop over a one-step returning/escaping body" contract,
  shared with input seek. This is reasonable as a note. `exists_inputSeekTM` uses `exit = none`
  and needs no join (`Build/InputCall.lean:241–244`).

How far this is from a proof: nothing of the target is formalized. The probe settles the exit join
and the ledger. What remains is the body leaf, its orbit invariant (by `roundOrbit_zero/_succ`),
the configuration decomposition and transport, and the window bookkeeping (`bufferTape_*`).

## (d) Environment (E1)

**What failed.** Line numbers refer to `logs/bootstrap.log`; excerpts are in `out/20`.
1. The unmodified pinned Lean failed with `error: failed to locate application` (l. 8–9). That is
   exactly the addendum's condition.
   - The shim fixed it: `Lean (version 4.25.0, x86_64-unknown-linux-gnu, commit cdd38ac5…)`
     (l. 11–12), with the shim's SHA-256 matching (l. 14–15).
   - **The shim was used as the addendum requires:** condition recorded, hash recorded,
     environment variables recorded, source included, `.so` excluded.
2. `lake exe cache get` printed "No files to download" and "Decompressing 7506 file(s)" (l.
   3049–3050).
   - 3,009 archives then failed with `No space left on device (os error 28)` (l. 35–3046).
   - Writing to stderr then failed too. leantar's Rust runtime panicked: `failed printing to
     stderr: No space left on device` (l. 737–739). One log line is corrupted by two paths merged
     into one (l. 734).
   - Result: `uncaught exception: leantar failed with error code 101` (l. 3051). Exit code 101 is
     Rust's panic code, so it follows from the ENOSPC.
3. The fresh bootstrap died on its first module, `Build/Zone`: `Bus error`, `lean exited with
   status 135`, no `.olean` produced (l. 3053–3058). Status 135 is 128 + 7, SIGBUS on Linux.
4. An exploratory check of `Build/Convention`, against cached oleans from another pin, gave the
   same SIGBUS 135 (l. 3060–3088).
5. The worker also notes that "The initial extraction and later dependency decompression exhausted
   disk space" (l. 3093). It reused a pinned runtime from a different scratch directory
   (`/workspace/scratch/edcf4c9982ed/…`; its own is `edf8bcbbbb4e`). It verified that runtime by
   the executable's hash only (l. 3091–3092; REPORT l. 31–33).

**Diagnosis.** The root cause is the worker host's full filesystem. The symptoms follow from it in
order:
- ENOSPC during decompression;
- the leantar panic (101) from writing stderr to the same full disk;
- a partial dependency build tree. About 40% of the 7,506 archives failed, and the rest may have
  been cut off mid-write.

The SIGBUS is not proven; there is no core file or kernel log. It is very likely a consequence of
the partial tree, because Lean mmaps `.olean` files and reading past the end of a truncated mapped
file raises SIGBUS. Three things point that way:
- `Build/Zone` imports only `Mathlib.Algebra.BigOperators.Group.Finset.Basic` and
  `Mathlib.Data.List.FinRange` (`out/13`), so the crash happened while loading Mathlib's oleans,
  before any TCSlib code.
- The same module elaborates on our host against the same pins (`oleans-lndnf` contains its
  replay olean).
- A second, unrelated module crashed identically.

This is not a toolchain or shim problem; `--version` worked. The stop under the addendum was
correct. Running the bootstrap and an exploratory check after a failed cache step could only crash,
and it adds a confounding symptom.

**Measured footprint** on the maintainer host, for sizing (`out/13`, `out/14`, `out/15`):

| Component | Size |
|---|---|
| Pinned toolchain, extracted | 2.3 GiB |
| Mathlib build tree | 5.1 GiB (oleans 4,477 MiB, `.c` 286, `.ilean` 204) |
| Other dependency build trees | about 0.35 GiB |
| `~/.cache/mathlib` | 1.1 GiB (several pins) |
| The 80 order-list oleans | 224 MiB |
| The checkout | 196 MiB |

The total is about 9–10 GiB, plus the toolchain archive during extraction.

The 80 modules reach only 1,427 dependency oleans, about 722 MiB, out of 7,167 Mathlib oleans
(4,477 MiB) (`out/15`). Their direct Mathlib roots are 35 modules (`out/16`). The list file also
holds a stray `the` from a comment; drop it.

**Proposed addendum changes** (a new section, "Resources", alongside the shim section):
1. **Disk preflight before toolchain extraction and before the cache step.**
   - Record `df -Pk "$HOME" "${MATHLIB_CACHE_DIR:-$HOME/.cache/mathlib}" . "${TMPDIR:-/tmp}"`
     (plus `uname -m`, `nproc`, `free -m`) in the bootstrap log.
   - Require at least **12 GiB** available for the full cache: the measured total plus about 30%.
   - If less is available, stop at once with "E-disk" and the `df` output. Extract nothing and
     decompress nothing.
2. **Cache placement.** Authorize `MATHLIB_CACHE_DIR=<dir on the clone's volume>` for the
   `lake exe cache` process only, recorded in REPORT.md.
   - Mathlib's `Cache/IO.lean:55–58` reads `MATHLIB_CACHE_DIR`, then `XDG_CACHE_HOME`.
   - It is an environment variable, not a permission or toolchain change, so it does not conflict
     with addendum rule 1. It is still worth naming explicitly.
3. **Optional scoped cache.** This needs a maintainer dry run on a clean clone before adoption; I
   did not run the cache tool. The command is `lake exe cache get <the order list's direct Mathlib
   imports>`. The cache CLI's help: "'get [ARGS]' will only get the cache for the specified Lean
   files and all files imported by one". For this order list that is about 722 MiB instead of
   about 4.5 GiB, and with it at least 5 GiB free suffices.
4. **Cache success gate.**
   - The cache step passes only if `lake exe cache get` exits 0 and its output contains neither
     `No space left` nor `leantar failed`.
   - Then elaborate a one-line smoke file, `import Mathlib.Data.List.FinRange`, through the
     `scripts/lean_check_tree.sh` `LEAN_PATH`. It must exit 0 before the bootstrap.
   - On any failure, stop. Never run the bootstrap or any probe against a partial cache; SIGBUS 135
     is the expected symptom.
5. **Recovery after freeing space.** Free space only by deleting the run's own files. Then force a
   full re-decompression with `lake exe cache unpack!` (the help text says "no skipping"). The
   alternative is to delete the clone's `.lake/packages/*/.lake/build` and run `get` again. Either
   way, no truncated olean from the failed attempt survives.
6. **Resource stop rule.** Stop at the first resource failure: ENOSPC, leantar 101, Lean 135
   (SIGBUS) or 137 (SIGKILL/OOM). Report the failing command, its exit code, and `df`/`du`.
   - No exploratory checks after it.
   - Never use oleans the run's own bootstrap did not produce, even exploratorily. This run used
     cached oleans from another pin (l. 3060–3063).
7. **Toolchain provenance.** Install the pinned toolchain into the run's own scratch, from the
   official release archive or elan, and record the archive's SHA-256. A runtime found elsewhere
   on the host is reused only after the whole archive is checked, not just the executable.
8. **Log hygiene.** Summarize the cache output (`… 2>&1 | tail -n 50`, with `PIPESTATUS`). The
   3,009-line flood is unreadable, and once the disk was full it corrupted itself (l. 734).

## (e) Other escalations / API gaps

- REPORT.md claims no mathematical obstruction and no missing public API. **That is true at the
  base, with one minor exception below.** The route's names resolve from InputWindow's import
  context:
  - the 49 issued checks (`out/10`);
  - 20 further names the route needs: `roundOrbit_zero/_succ`, `inputSymbolInner`, `Cfg.ext`,
    `embedEmitTM_tr`, `embedEmitCfg_state/_inputPos/_output`, `MultiTapeTM.AgreeOn`,
    `runFrom_eq_of_agreeOn`, `step_eq_of_agreeOn`, `runFrom_mapState_of_agreeOn`,
    `Cfg.mapState_apply`, `counterLoop_time_le`, `counterOverhead_succ/_zero`,
    `CounterLoopState.escape/.done`, `counterLoopStateFintype`, `Fin.lastCases` (`out/11`).
- The one non-resolving pair is `phaseHostTM` / `phaseHostTM_run`. That is a **route** defect, not
  an API gap; see (a), item 1, and (c).
- **Minor API gap: `MultiTapeTM.AgreeOn` (`Simulation.lean:1120`) has no published introduction
  equation.**
  - Using `runFrom_eq_of_agreeOn` requires introducing it, which under rule 10 strictly means
    unfolding another file's definition.
  - Precedent: `StateRenaming.lean`'s `runFrom_mapState_of_agreeOn` and `CounterLoop.lean`'s
    `counter_refl_agree` introduce it by `intro`.
  - Draft, probed (`MultiTapeTM.agreeOn_iff_probe` in `probes/IWReviewJoin.lean`; with it,
    `iwProbe_join_prefix'` compiles; `out/12`):

    ```lean
    theorem MultiTapeTM.agreeOn_iff {k : ℕ} {Symbol State : Type*}
        (M N : MultiTapeTM k Symbol State) (Q : Set State) :
        M.AgreeOn N Q ↔ ∀ q ∈ Q, ∀ inp work, M.tr q inp work = N.tr q inp work :=
      Iff.rfl
    ```

## (f) Recommendation

**I confirm the default policy: do not land this delivery.** It is a docstring-only appendix
blocked by the environment. Its one concrete route claim, the `phaseHostTM_run` join, is unusable
without an import that rule 6 forbids, and it carries run narrative into a library docstring.
Nothing in it is lost by not landing: REPORT.md and this review hold the content. Carry the
following into **C1-WC cont1**.

1. **Keep:**
   - the one-tape body (anchor `false`, escape `true`);
   - `τ = 1`, `r₀ = |y|` on escape, `d = |y|` on exhaustion;
   - the endpoint words: all `true` on exhaustion, `counterWord w (|y|+1)` on escape;
   - **`C = 6`** with both ledgers (probe-verified, `out/12`);
   - the four edge cases;
   - the promotion-candidate note.
2. **Replace the exit join.**
   - State that `Build/Seam` is outside the import closure: `Unknown identifier`, `out/11`.
     `phaseHostTM` / `phaseHostTM_run` may not be used, and no import may be added.
   - Prescribe instead the brief's "one-step join" as a private `iw_` leaf. The table is
     `counterLoopTM`'s, with `.escape` going in one stationary silent step to `.done`.
   - The prefix comes from `MultiTapeTM.runFrom_eq_of_agreeOn` with `Q = {q | q ≠ .escape}`. The
     join step comes from `step_of_some` and `Action.apply_*`.
   - Attach `probes/IWReviewJoin.lean` as the worked pattern, labeled as the maintainer's probe.
     The fill must not transcribe it verbatim; the duplication rules apply.
   - Say explicitly that this is not a second seam: it delegates to the loop's table, under ground
     rule 7.
3. **Decide the `AgreeOn` introduction** before issue. Either authorize `intro` on
   `MultiTapeTM.AgreeOn` in the brief, citing the two precedents, or land `MultiTapeTM.agreeOn_iff`
   (above, `Iff.rfl`) through the API-PR route first. The strict reading of the "Everything" rule
   favors the API lemma.
4. **Fix the brief's body wording:** a one-tape body on `dst`; `counterLoopTM` adds the counter as
   tape `Fin.last 1`; the loop is embedded along `ι : Fin 2 ↪ Fin k` with `0 ↦ dst` and `1 ↦ j`.
5. **Extend the import probe** with the route names beyond the 49 that resolve in `out/11`. The
   minimum: `roundOrbit_zero/_succ`, `inputSymbolInner`, `Cfg.ext`, `embedEmitCfg_state`,
   `_inputPos`, `_output`, `MultiTapeTM.runFrom_eq_of_agreeOn` (and `agreeOn_iff` if landed).
6. **Base.** `83ec6348` is still valid for InputWindow; its Lean equals `75edca6f` (`out/07`). If
   cont1 is issued at a newer tip, rerun the pre-ship check (file elaboration plus the extended
   probe) there.
7. **Environment.** Attach the revised addendum from (d), items 1–8, and dispatch only to a host
   that passes the 12 GiB preflight (or 5 GiB with the scoped cache, once dry-run).
8. **Appendix content for whatever lands later:** proof content only. Run-specific status ("the
   bootstrap crashed", "this continuation") belongs in REPORT.md.
