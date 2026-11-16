# DW-5 · derand F-01: typed-view readers, then E1 and `polyTimeComputable_find` re-derived through them

**Result.** F-01's 20 Rule-10 seal failures (9 in E1 `computesFunInTime_find`, 11 in `polyTimeComputable_find`) are
cleared: the `IterateFind` seals give **0 errors in all four variants** (strict and coe, A and B), against 20 in each at
the base. The readers add no seal failure. The two reader owners, however, carry **26 pre-existing seal failures**
(ModuleHost 10, IterateFindHost 16) in declarations this change does not touch. Clearing those needs frozen-file changes
beyond the readers, so they are left as a scope question (below). Build, state check, axioms, admissions, statements, lint
and name clash are clean, and `dl-oleans-2` is restored to the snapshot.

Date: 2026-11-16 UTC. `$SP` is this session's scratchpad. All evidence is in `dw5-evidence.zip` under `dw5/`. Its
SHA-256 and every entry are listed in `SHA256SUMS`.

## Branch (local only, never pushed)
- **Branch:** `cleanup/dw5-derand-readers`, made in the limited worktree `$SP/wt-dw5` from the records tip.
  - The worktree was sparse: non-cone `/*`, without `briefs/`, `dataset/`, `blueprint/`, `dep_graph.json` and the PDF.
  - The records tip was taken with `git fetch origin cryptography/pass-shelat-ch2-4` by name:
    `2da7e0f3cd65ec93ed71813b7828c3b66ba18942`.
- **Commits** (both carry an SSH signature header; the signatures cannot be verified here because no
  `allowedSignersFile` is configured; files were staged by explicit path):
  1. `1da80d9a952c3da3e406f58188cca66de94cbfaf`: the readers (ModuleHost +97, IterateFindHost +30/−2).
  2. `daa6e173cdd94cad1475b9a96eca613bce53ba61` (**head**, tree `2ae32eb3`): the re-derivations (IterateFind +126/−294).
- In total, 3 files change, with 253 insertions and 296 deletions (`branch/`).

## The readers (formula docstrings; `rfl` or the original contract as proof; no `@[simp]`)
`TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean`, namespace `Turing.ModuleHost`, in a new section
"The typed view of the host":
- `abbrev hostTMView M K hk ctrl ret q₀ : FinTM Bool` is `⟨K, State C M, (hostTM M K hk ctrl ret q₀).tm⟩`.
- `hostTMView_eq : hostTMView M K hk ctrl ret q₀ = hostTM M K hk ctrl ret q₀ := rfl`.
- `hostTMView_q₀ : (hostTMView M K hk ctrl ret q₀).tm.q₀ = q₀ := rfl`.
- `hostTMView_step_inl` is `hostTM_step_inl` for the view: `cfg.state = some (.inl c) →
  (hostTMView …).tm.step cfg = (ctrl c cfg.inputSymbol cfg.workTapeSymbols).apply cfg`. Its proof is `hostTM_step_inl …`.
- `host_call_view` is `host_call` for the view, with the same hypotheses and conclusion. Its proof is `host_call …`.
- `host_clean_view` is `host_clean` for the view. Its proof is `host_clean …`.

`TCSlib/Complexity/Randomized/Build/IterateFindHost.lean`, namespace `Complexity.IterateFind`:
- `abbrev copyTMView : FinTM Bool` is `⟨1, Fin 2, ⟨0, copyTM.tm.tr⟩⟩`.
  - This view makes the start state `0` explicit as well, because `host_call_view`'s hypotheses start the module at
    `(M i).tm.q₀`.
- `copyTMView_eq : copyTMView = copyTM := rfl`.
- `copy_clean_view (x)` is `copy_clean x` for `copyTMView`. Its proof is `copy_clean x`.

These are the SR-02 proposal (`fills/derand/final-r1/review-evidence.zip`, `logs/delivery-extracts/scope-request/SR-02/`)
with one change: `copyTMView` fixes `q₀ := 0`, where SR-02's view reused `copyTM.tm`. Both modules' docstrings list the
new declarations. No existing declaration, definition, proof or attribute changes in either file.

## The re-derivations (proof-only; IterateFind)
- **E1 `computesFunInTime_find`.**
  - The host is `ModuleHost.hostTMView M (K + 1) hk (hostCtrl M K) (hostRet M) (entry M 0)`, and module 0 is
    `copyTMView`.
  - The calls go through `host_call_view` and `host_clean_view`, and the start state through `hostTMView_q₀` and
    `initCfg_ofWords`.
  - The three control steps (dispatch, branch, halt) are derived in the proof from `hostTMView_step_inl` and
    `hostCtrl_eq`. Seams are read through the published `Cfg.ofWords_*` readers and `stateWord_eq`.
  - The loop combinator's result is matched by cases on the search, which removes the 9th, matcher-transport failure.
  - The module now builds with 0 warnings; at the tip it had 12, from unused simp arguments.
- **`polyTimeComputable_find`** is re-derived **from E1**, with `init = id`, fuel `R.eval` and the same fuel machine as
  before; `final_bound` is kept as its normal form. This is derand F-03's pre-approved re-derivation, and it removes
  E1's 196-line repetition of the old assembly.
  - The theorem moves below E1, which it now uses. Its header and prose are byte-identical.
  - The frozen check (`statements/frozencheck.txt`) reports exactly that one ORDER difference, and no header, prose or
    body difference. Its control (`frozencheck-control.txt`) detects a one-character prose change.
- **Sketches.** Both proof sketches were refreshed, because the route changed. The statement paragraphs are unchanged.

## Checks (tree `$SP/dl-oleans-2` only; one Lean process at a time; no lake, no cache get)
- **Preflight.** The snapshot (`tree/snapshot-pre.txt`) has 1230 files and SHA-256
  `457ba704d26757307f14131aa534929ffd70d30a732b0c744b104ca3fc96a15f`, as required. `$SP/dl-oleans` was not touched.
- **Build** (`build/`). The sc-yao and int-tip method, with unmodified copies of the tools (`tools-used/`):
  - **Order and plan.** `downorder.py` against the snapshot base `eff2dcd0` gives changed 183, down 706 and order 1342.
    The order is the closure of root `TCSlib` and both `audits/*/Checks`.
  - **State.** `stateplan.py init` keys 1199 modules, and its `state-init.json` is byte-equal to int-tip's.
  - `plan` gives 706 to build (563 snapshot oleans and 143 new) and 636 to reuse.
  - **Mathlib.** The overlay (3346 symlinks) plus NthRootLemmas (olean `c0a9cff0…`), the only missing Mathlib root.
  - **Backup.** A hard-link copy of all 1230 snapshot files, hash-checked.
  - **Result:** 706/706 rc 0. `error:` 0, `error(` 0, combined 0, and the substring "error" 0 (`build/per-module.tsv`).
  - Sorry warnings: 91.
  - Runtime: 6417 s of module time, 19:57–21:44 UTC. Max RSS was 4.49 GB, and the lowest free disk was 1542 MB.
- **State check.** `update` took 706 modules, and `check` over the 1342-module order gives 1342/1342 OK, RESULT OK
  (`build/statecheck.txt`).
- **Rule 10** (`rule10/`, driver `tools-used/rule10_dw5.sh`; `rule10_b.sh` and the archived Gate 06/10 harness
  unmodified; `lean -DmaxErrors=0`; both error forms counted).

  | Owner | Requests (A/B) | Errors at the base (each variant) | Errors at the head: strict A, strict B, coe A, coe B | Install / EOF |
  |---|---|---|---|---|
  | IterateFind (F-01) | 595 / 596 | 20 = E1 9 + `polyTimeComputable_find` 11 | **0, 0, 0, 0** | yes |
  | ModuleHost | 241 / 241 | 10 (pre-existing) | 10, 10, 10, 10: identical to the base, none in a reader | yes |
  | IterateFindHost | 251 / 251 | 16 (pre-existing) | 16, 16, 16, 16: identical to the base, none in a reader | yes |

  - **The baseline is F-01's 20.** The tip baseline (`base-seals/`) has the same 20 messages at the same positions as
    the derand review's F-01 log.
  - **Head against base** (`compare/seals-base-vs-head.txt`):
    - Every request row is identical.
    - IterateFind: all 20 are cleared, and nothing is new.
    - The reader owners' failures are identical in declaration and message.
  - **Strict and coe** probes are byte-identical, because no projection-coercion instance is in these closures.
  - **The typed views** are reducible abbreviations. The seal excludes them as notation (`term_excluded: abbrev`),
    while `hostTM` and `copyTM` stay sealed rows.
  - **Paired controls** (`tools-used/mkctl_dw5.py`, the derand generator's harness, with one row per new reader):
    - Each harness has 8 probes and gives ALL_OK True, in strict and in coe.
    - The 29 expected sealed negatives fail exactly once each. The negatives are the `rfl`/definitional transports
      through `hostTM` or `copyTM`.
    - The readers pass, the unsealed probes give rc 0, and there are no stray errors.
  - **Explicit-unfold scan** (`scan/`):
    - Touched declarations: 128 items and **0 foreign**.
    - The three files have 27 pre-existing foreign items. They are identical at the base (`scan/scan-base-vs-head.txt`)
      and all sit in IterateFindHost's untouched `copy_*` and `host_branch` proofs.
- **Axioms** (`axioms/`, the derand census probe with the readers added).
  - The two re-derived theorems, the 9 readers, and everything F-01/derand cited downstream use only `propext`,
    `Classical.choice` and `Quot.sound`. That covers 27 printed constants, among them
    `polyTimeComputable_iterateFind`, `exists_seedMajorityTM`, `seedMajority_mem_DTIME`, `bpp_subset_dtime_subexp`,
    `inBPP_iff` and the Derand helpers.
  - The census of the three owners has 193 stored constants, all standard. `sorryAx` does not occur.
- **Admissions** (`admissions/`, `tipcensus.py`; each module's sorry count is taken from build records whose source matches
  it): 229 at the tip and 229 at the head, identical per module.
  - The three changed modules have 0 at both revisions, and none of the three files contains `sorry`.
  - The same 34 modules have no record at either revision; they lie outside the order.
- **Statements** (`statements/decls2.tsv`): 9 ADDED (exactly the readers above), 0 CHANGED, 0 REMOVED.
- **Lint** (`lint/`).
  - `campaign_style_lint.py TCSlib/Complexity` gives 25 FAIL and 338 WARN at both the base and the head; only INFO lines
    change (file sizes and declaration counts).
  - `style_lint.py --area Complexity` gives identical output.
  - All lines are within 100 characters, and there is no trailing whitespace.
- **Name clash** (`checks/nameclash.txt`): 0 exact full-name clashes. The 9 new names have no same-short-name declaration
  elsewhere.
- **Restore** (`restore/`):
  - Of the snapshot files, 41 were restored and the other 1189 were unchanged.
  - The 143 new oleans and the Mathlib overlay (3346 symlinks and 1 file) were deleted.
  - **SNAPSHOT EQUAL** (`457ba704…`). restoreplan reports extra 0, changed 0 and missing 0.
  - An independent recheck gives the same: SNAPSHOT EQUAL; 0/0/0; no symlinks, no `Mathlib/` and no empty directories.
  - Then the backup, the probes and the worktree were removed, and the branch was kept (`cleanup.txt`).

## Disclosures
- **Duplication.**
  - E1's proof derives the three control steps (`hdisp`, `hbranch`, `hhalt`, about 30 lines) at the typed view from
    `hostTMView_step_inl` and `hostCtrl_eq`. This restates the content of the public `host_dispatch`, `host_branch` and
    `host_halt`.
  - Those originals cannot be used at the view, because their statements read `hostTM`'s fields by definition.
  - The readers `host_call_view`, `host_clean_view`, `hostTMView_step_inl` and `copy_clean_view` restate `host_call`,
    `host_clean`, `hostTM_step_inl` and `copy_clean` at the typed views, by design, as in SR-02.
  - Net effect: E1's 196-line repetition of `polyTimeComputable_find` (F-03) is gone.
- **No longer used.** Nothing in the library now uses `IterateFind.host_dispatch`, `host_branch`, `host_halt`,
  `IterateFind.hostTM` or `copyTM_k`. The private `dupWord_poly` is now unused too. It is kept, because deleting it would be
  a REMOVED statement.
- **Order.** `polyTimeComputable_find` moved below E1, as described above.

## Scope question (for Seyoon)
Both reader owners became "changed owners" by gaining the readers, and their whole-file seals show 26 pre-existing
failures, unchanged by this work:
- **ModuleHost (10):** `stop_step`, `stop_clean`, `clean_install`, `clean_emit`, `pad_seam`, `pad_apply`, `pad_run`,
  `host_seam` and `host_call`.
- **IterateFindHost (16):** six in `copy_step`, `copy_turn`, `copy_rewind`, `copy_finish` and `copy_clean`, and ten in
  the **statements** of `host_dispatch`, `host_branch` and `host_halt`. Those statements type `(hostTM M K hk).tm.step`
  on `Cfg.ofWords (.inl c) …`, which needs `hostTM`'s `State` field by definition.
- The same untouched IterateFindHost proofs hold the scan's 27 foreign explicit items.

Clearing them needs proof changes in these frozen files, and for the three `host_*` statements a statement change or
their replacement by typed-view versions. That is beyond the readers, so nothing was done. Options:
- (a) **Recommended:** record them as a new deferred item, gated separately, and take DW-5 as clearing F-01's 20.
- (b) Extend DW-5 to clear them, with Seyoon's approval of the frozen proof edits and of a statement route for
  `host_dispatch`, `host_branch` and `host_halt`.

## Layout of `dw5-evidence.zip` (`dw5/`)
- `branch/`: branch facts, raw diff, per-commit diffs and the head sources of the 3 files.
- `tree/`, `order/`, `plan/`, `state/`, `build/`, `build-mathlib-extra/`: preflight, order, plan, state, build records
  and logs, and the state check.
- `base-seals/`: the tip baseline seals (collector, probes, logs, `touched-tip.json`).
- `rule10/`: head collector, axioms probe, seals strict/coe A/B, controls, ctlcheck, sealsum and probe sources.
- `compare/`, `scan/`, `axioms/`, `admissions/`, `statements/`, `lint/`, `checks/`.
- `restore/`, `restore-pre-delta/`, `cleanup.txt`.
- `dev/`: non-canonical development iterations on uncommitted sources (`devseal.py`/`devcheck.sh`). The reported
  results are the head runs above.
- `tools-used/`: every script run.
  - Unmodified copies: int-tip's build tools and gate40-seals-merged's seal suite (`seal/`).
  - New for this job: `rule10_dw5.sh`, `mkctl_dw5.py`, `run-build.sh`, `diskwatch.sh`, `restore-dw5.sh`,
    `seals_dev.sh`, `devseal.py` and `devcheck.sh`.
  - Copied from the derand review: `frozencheck.py`. Copied from sc-yao: `nameclash.py`.
