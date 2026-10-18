# Gate 46 review: PR #124 round 2, the seam-layout contract (`Build/SeamLayout`) (PASS 0/0/1/11)

Reviewer: read-only review sub-agent, 2026-10-18. `$S` is the scratchpad; `$Z = $S/review/gate46`.
Every claim cites a saved output under `$Z/outputs/` (or `$Z/edit/`).

**The PASS stands: 0 blockers, 0 majors.** Every finding is true at its stated severity. The one
minor concerns the PR description only, so it needs **no `.lean` change**: no commit on #124 and
no re-replay. My fix also covers three stale points the auditor did not list (X1).

**#124 (`lean/seam-layout` at `45b79f5f`): not yet clear to merge.** It becomes clear once two
things are done: gate 46's records are committed (the patch in (b)), and the PR description is
replaced by the corrected body. The replay `replay-lseam2` passed at `45b79f5f`, and the merge
result's `TCSlib/` tree equals the replayed tree at the current tip. One condition: merge #124
before #130 and #131 (see (d)).

## Inputs

| Input | Value | Evidence |
|---|---|---|
| Bundle | `exchange/archive/gates/46-seam-layout-statements-r2-gate/seam-layout-statements-r2-bundle.md`, SHA-256 `301f6081…a347` (matches `SHA256SUMS`; the README's SHA also OK), 1,633,456 bytes. 53 `## ===== … =====` sections, in `BUNDLE-FILES.txt` order. Its SeamLayout, facade, Catalog and Seam sections contain the head's files verbatim | `outputs/bundle-check.txt` |
| Findings | `$S/wt-hk/campaign/gates/43-seam-layout-statements/findings-r2.md`, read as data. Committed verbatim at `b175e512`, the records worktree and the campaign tip | — |
| Lean head | `45b79f5feeabfe58c5a66c991f7a95994dc723dd`. Its parent is `f92fb961` (round 1), whose parent is `5fd5dce8` (#126). It changes exactly 2 `.lean` files, with blobs `d0af5ae6` (SeamLayout) and `87ebb353` (facade) | `outputs/freeze-check.txt`, replay pins |
| Live PR | #124 is OPEN, at head `45b79f5f`, with base `complexity/arora-barak-ch3-4`, MERGEABLE. Its body is identical to `r2/pr-body.md` (the record has one extra trailing blank line) | `outputs/pr124-live.json`, `outputs/pr124-live-vs-record.diff` |
| Stack | #122, #123, #125, #126 and #128 are merged. The `TCSlib/` tree is `06d30610` at `5fd5dce8`, at `45b79f5f~2` and at the tip `b175e512`. `git merge-tree` of the head into the tip gives the head's `TCSlib/` tree (`a8174885`) | `outputs/stack-prs.txt`, `outputs/tip-equivalence.txt` |
| Elaboration (mine) | `leanelab.sh $S/wt-seam-b $S/oleans-lx2b`, one at a time: the module (exit 0, one warning: `sorry` at 96:8), then the round-2 probe copied to `outputs/probe/` (exit 0, `sorry` only at the inline contract 21:8; the axioms are the recorded ones) | `outputs/elab-head-vs-lx2b.out`, `outputs/consumer-r2-vs-lx2b.out` |

**The records worktree moved during the review**, from `b175e512` to `2df1add6` (gates 47–49's
packs). The gate-43 folder and the seam-layout evidence are unchanged, the `TCSlib/` tree is still
`06d30610`, and the records patch still applies (`outputs/records-patch-applycheck.txt`,
`outputs/merge-order.txt`).

One side effect to note: I ran a `git fetch origin complexity/arora-barak-ch3-4` in the main
repo, which may have moved that remote-tracking ref (it now reads `b175e512`). There were no other
writes outside `$Z`.

## (a) The findings at the head

| # | Auditor | Verified | Grade | Basis |
|---|---|---|---|---|
| 1 | minor | **true** | minor | The live body still has: line 17, "U2-S's private leaf is promoted"; line 40, checks "against `oleans-lndnf`"; lines 45–46, `replay-lseam.sh` "from `oleans-lc1w`"; line 32, "eight exact `_run_ofCfg` contracts and two named leaves". The sketch at `SeamLayout.lean:60–89` has 8 phases: 6 rows (phases 1, 2, 5, 6, 7, 8) and 2 leaves (phases 3, 4). The pack and resolutions say `replay-lseam2.sh` from `oleans-lx2b`, elaborated against `oleans-lc1w` (`gate43-review.md:18`). The two `.lean` files have no such text (`outputs/minor1-locations.txt`) |
| 2 | note | **true (checked)** | note | Bundle SHA, 53 sections, all 15 `r2/SHA256SUMS` files OK, blob pins `d0af5ae6`/`87ebb353`. Comment-stripped code: the r2 draft equals the head. Round 1 → head changes only the binder and quantifier lines (stripped lines 11–18), and the endpoint clauses are unchanged. 1 declaration, 1 `sorry` (`outputs/freeze-check.txt`) |
| 3 | note | true (read; its arithmetic checked) | note | `T ≤ 7n + 18 ≤ 18(n + 1)`. Every row is silent with `inputMoveAction 0`. `phaseHostTM` tags states by phase (`Σ i, Ph i`, `Seam.lean:832`), so the last phase's `done` is fresh |
| 4 | note | **true (checked)** | note | `skipTM_run_ofCfg` (`Catalog.lean:12240`): `|w| + 1` steps, head at `pos + |w| + 1` = `n + 1`. `skipBackTM_run_ofCfg` (`:12302`): its start `pos − |u| − 1 = 0`, cells `−1..n` = `bufferTape s`, `n + 3` steps. `pairEncode` (`Encoding.lean:135`) is doubled bits, then `[false, true]`, so `h` steps |
| 5 | note | **true (checked)** | note | `walkTM_run_ofCfg` (`:12155`) at `dir = .neg`, `w = m.reverse`: cell `q + 2 − p` = `m[q − p]`, cell 1 blank, `q + 2` steps. `transferTM_run_ofCfg` (`:1372`): relative `−1` is phase 4's blank, `|v|` is the right blank, `2|v| + 2` steps, heads unchanged. `tbl` was blank, so its endpoint is exactly `bufferTape v` |
| 6 | note | **true (checked)** | note | Phase 7 starts at `0` (`h + q + 1 − (h + q) − 1`). `clearTM_run_ofCfg` (`:1520`): `2(h + q) + 2` steps, head kept at `0`. The ledger, summed per phase over 16,000 cases, equals the closed form; the slack is `h + 3|v| + r`; `T ≤ 18(n + 1)`: 0 failures (`outputs/ledger-check.txt`) |
| 7 | note | true (read) | note | `seamLayout_u2s` takes `r = |serializeK (E.machine α)|`, so `T` is chosen per `α` before `w`. It projects table, summary, source, heads and input position. Re-elaborated against `oleans-lx2b`: OK |
| 8 | note | true (read) | note | `seamLayout_rep_fields` uses `embedSilentCfg_cap` at the `[]` prefix, `outputSummary_nil`, `summaryCells_eq` and `FinTM.bufferTape_of_neg` (no stand-in). The `Rep_iff.mpr` example takes the bank and input fields as hypotheses. Re-elaborated: OK |
| 9 | note | **true (checked)** | note | `sim_route.py` and `sim_contracts.py` (default 14,400; `4 6` gives 110,887) re-run with `python3 -I`: the same 3 result lines as the records (`outputs/sim-compare.txt`). The four adversarial times are 37, 34, 66 and 49 by the closed form. The probe's inline contract is byte-identical to `SeamLayout.lean:96–118` (`outputs/probe-contract-match.txt`) |
| 10 | note | **true (checked)** | note | The TCSlib closure is 17 modules; it has no StepBlock, CodeSimulator, UniversalK, NDCodeSimulator or UniversalStartup (`outputs/import-closure.txt`). The facade imports and lists the module |
| 11 | note | **true; now reproduced** | note | The replay log and static file equal the `$S/fills/replay/` copies (SHA). The replay list is the 2 modules, without the root. `oleans-lseam2` holds `SeamLayout.olean` (`outputs/replay-identity.txt`). I reran the module and the probe fresh against `oleans-lx2b` (Inputs) |
| 12 | note | **true; reproduced** | note | `campaign_style_lint.py TCSlib/Complexity/TuringMachine` at the head gives `0 FAIL, 63 WARN over 80 files` (`outputs/lint-head.txt`). It differs from `r2/lint-r2.txt` only in `ZoneRebalance.lean`'s INFO rows (571 → 861 lines, from #125's `e6917ea0`): `lint-r2.txt` was taken on the pre-restack base. The totals are unchanged (`outputs/lint-head-vs-record.diff`) |

**Reviewer additions** (not in the findings):

- **X1 (records; folded into minor 1's fix).** Two more stale points in the live body:
  - Lines 19–21: "Stacked on #126 … Merge #122, #123, #125 and #126 first". All four are merged,
    and the base is the campaign branch.
  - Lines 4 and 34: two `audits/…` paths that moved on 2026-10-18 (`MOVED.md:1065`, `:1120ff`).
  - Also line 11, "U2-S (in flight) plans that split privately": U2-S delivered (#130) and built no
    split leaf (resolutions, round-1 rulings).
- **X2 (note).** `r2/lint-r2.txt` and `r2/elab-r2.out` predate the restack (`oleans-lc1w` base).
  Both are reproduced at the head and the tip (rows 11 and 12). The corrected body says so in one
  clause. No action beyond that.

## (b) The minor's fix: records and the PR description only (no `.lean` edit)

**No `.lean` change.** The module's docstring already counts correctly
(`SeamLayout.lean:62–65`: "Eight phases … Each is a catalog row … or one of two leaves").
So there is no patch to elaborate and nothing to commit on #124.

**The PR description.** The corrected body is `edit/pr124-body-corrected.md` (SHA-256
`d02cecdc…1b62`); the diff against the live body is `edit/pr124-body.diff`. It was produced by
`scripts/body_edits.py`: 7 replacements, each asserted unique, with assertions that no stale text
remains and that every new line is at most 100 characters (`outputs/body-edits.txt`).

| # | Live lines | Stale | Replacement |
|---|---|---|---|
| E-1 | 4 | `audits/evidence/c1/fills/core-1/REVIEW.md` | `campaign/fills/c1/reviews/core-1/REVIEW.md` |
| E-2 | 11–12 | "U2-S (in flight) plans that split privately" | "U2-S's startup, H1's sketch and R's route need it." |
| E-3 | 14–17 | the 2026-10-17 ruling with "U2-S's private leaf is promoted" | both rulings: the 2026-10-17 one (R and UN cite it), and the 2026-10-18 one: a standalone fill after this gate, along the eight-phase sketch; U2-S's continuation may import and cite it; supersedes the promotion (#130 built no split leaf) |
| E-4 | 19–21 | "Stacked on #126 … Merge … first" | "Base: the campaign branch", the four merged, `5fd5dce8`'s `TCSlib/` tree equal to the tip's |
| E-5 | 31–34, 38 | run-on paragraph; "eight exact `_run_ofCfg` contracts and two named leaves"; the `audits/…/r2/` path | paragraph break; "eight phases by `phaseHostTM`: six catalog rows through their exact `_run_ofCfg` contracts and two named leaves"; `campaign/items/c1/seam-layout/r2/`; a **Gates** line: round 1 FAIL 0/2/1/7, round 2 PASS 0/0/1/11 |
| E-6 | 40–46 | round-1 checks (`oleans-lndnf`, `replay-lseam.sh` from `oleans-lc1w`) | round-2 checks at `45b79f5f`: elaboration against `oleans-lc1w` (the same against `oleans-lx2b`); probe; lint; `replay-lseam2.sh` from `oleans-lx2b`, passed 2/2, static-equal (1); round 1's checks marked superseded, their records kept |

Apply it with `gh pr edit 124 --body-file <corrected body>`. This modifies the PR, so the
maintainer or the user runs it.

**Records** (campaign branch, a direct push of non-`.lean` files). The patch is
`edit/records-gate46.patch` (SHA-256 `105c913c…b193`). It was produced by
`scripts/records_edits.py` with asserted anchors, and `git apply --check` passes on `b175e512` and on `2df1add6`
(`outputs/records-patch-applycheck.txt`).

| # | File | Edit |
|---|---|---|
| R-1 | `campaign/gates/43-seam-layout-statements/resolutions.md` | Round 2's Replay bullet gets its result: passed (user, 2026-10-18), 2 of 2 at `45b79f5f`, static-equal (1) |
| R-2 | same | A new section, "Round 2: PASS (0/0/1/11)": the findings and review paths; minor 1 → fixed in the records, with its supersession recorded (round 1's `pack.md`, `findings.md`, `pr-body.md` and `gate43-review.md`, and `r2/pr-body.md` as dispatched, all preserved); notes 2–12 → no action, with 3–9 carried to the fill brief; the gate closes |
| R-3 | `campaign/items/c1/seam-layout/r2/pr-body-gate46.md` (new) | The corrected body under a one-line header. `r2/SHA256SUMS` stays as dispatched |
| R-4 | `campaign/items/c1/seam-layout/gate46-review.md` (new) | This file (R-2 cites it) |

Suggested backlog line: "Gate 46 (#124 round 2) PASS 0/0/1/11: reviewed; minor 1 (the PR
description) fixed in the records; #124 clear to merge after the body edit; the standalone fill's
brief carries (c)."

## (c) Carry-forward for the standalone fill brief

Route (from notes 3–6, checked above):
- **Phases, exactly as the docstring gives them:** skip, skip back, `pairSkip`, `unarySplit`, the
  walk on `sm`, transfer, skip back, clear.
  - **Seven dispatches**, and no extra rewinds after transfer or clear. Clear's `done` is the exit.
  - **The time is closed form, fixed before `d`:**
    `T = 2n − r + 4h + 5q + 2|v| + 23` with `h = 2|a| + 2` and `n = h + q + 1 + |v|`.
  - **Per-phase ledger:** `n − r + 1`, `n + 3`, `h`, `q + 3`, `q + 2`, `2|v| + 2`, `h + q + 3`,
    `2(h + q) + 2`.
  - **The constant:** `C = 18`, from `T ≤ 7n + 18` (slack `h + 3|v| + r`).
- **The host's last phase is not covered by `phaseHostTM_run`.** That lemma needs a redirect at the
  end state (`hred`). Run phase 8 through `MultiTapeTM.runFrom_mapState_of_agreeOn`
  (`StateRenaming.lean:158`, public, in the closure), with the trivial guard `red 8 · = none`, as
  `phaseHostTM_run`'s own proof does.
  - StepBlock instead uses a terminal `.halt` phase. That costs an eighth dispatch, `T + 1`, and
    would contradict the docstring's ledger, so do not use it.
  - Each of the seven joins rewraps `c'.mapState (fun _ => q')` as
    `c_next.mapState (Sigma.mk i')` (`Cfg.ext`).
- **The phase key and instances:** follow StepBlock's precedent (`StepBlock.lean:2202–2283`): an
  inductive key, `abbrev Ph`, and `cases key <;> dsimp [Ph] <;> infer_instance` for `Fintype` and
  `DecidableEq`.
- **Silence for all `u ≤ T`.** The rows' `_run_ofCfg` contracts give the output only at the
  endpoint (`{ d with … }`). Derive the per-time clause from `MultiTapeTM.output_prefix`
  (`Finite.lean:127`) sandwiched by the endpoint equality, or from table-level silence. The leaves'
  contracts must state it themselves.
- **The leaves.**
  - Each needs a framed contract with an exact time, no earlier `done`, unchanged other
    tapes/heads/input position, and silence.
  - `pairSkip` remembers only the first bit of each pair, and its separator step both moves and
    enters `done`, giving exactly `h` steps.
  - `unarySplit` writes `false` on `sm` with that head staying, and blanks `src` at `h + q` while
    moving right. The unary terminator is not restored on `src`.
  - If the leaves are public, each needs a lemma beside it (lint check 8). The duplication screen
    should confirm the docstring's "no row serves" claims.
- **Word identities.** `s.drop r`, `s.take (h + q)`, the cells of `m` and `v`, and the blanks are
  needed through `pairEncode_eq`, not `serializeK_eq`, which is outside the closure. The same
  identities exist only as **private** lemmas in `StepBlock.lean`: `bufferTape_suffix` (2763),
  `bufferTape_reads` (2585), `bufferTape_outside` (2062) and `bufferTape_unary` (2025). That module
  is outside the closure. The duplication ledger has no entry. The brief should choose one of:
  - local private copies plus a ledger entry, for the maintainer's dedup window (recommended:
    smaller replay); or
  - an API PR that promotes them to `Simulation.lean`'s `FinTM.bufferTape` API.
- **Imports.** Keep the closure free of StepBlock, CodeSimulator, UniversalK and NDCodeSimulator,
  so that U2-S's continuation can import `Build/SeamLayout` without a cycle (note 10). A fill-time
  check: the 17-module closure, `outputs/import-closure.txt`.
- **Frame.** Prove the full triple `Function.update` endpoint, not just the three tapes: R relies on
  it for the bank fields, including an installed choice tape (note 8). Also prove `inputPos`
  unchanged; input rewind and scratch cleanup stay U2-S's own phases (note 7).
- **Edge cases for the brief's checks** (note 9 and the rows):
  - `r = n` (skip over `[]`, 1 step);
  - `q = 0` (walk over `[false]`, 2 steps; `unarySplit` in 3);
  - `v = []` (transfer in 2; cell `n` is the right blank);
  - `a = []` (`h = 2`);
  - the times 37, 34, 66 and 49 for the auditor's four instances;
  - an extra populated tape with a negative head position preserved;
  - all-`false` table bits.
- **Natural-number casts:** `(r : ℤ) + ((n − r : ℕ) : ℤ) + 1 = n + 1` needs `r ≤ n`
  (`push_cast`/`omega`).

## (d) Bottom line

- **The PASS stands** (0/0/1/11). All 12 findings are true at their severities. I independently
  reproduced notes 2, 4–6, 9, 10, 11 and 12.
- **The minor is records-only:** the PR description. There is no `.lean` commit on #124 and no
  re-replay.
- **#124 is clear to merge once:**
  - the records patch (R-1 to R-4) is committed; and
  - the PR description is replaced (E-1 to E-6).

  The replay `replay-lseam2` passed at `45b79f5f`, and the merge result is the replayed tree at
  the current tip.
- **Merge order:**
  - #129 (`NTimeHierarchy.lean`) does not interact with #124.
  - #130 changes `UniversalK.lean` (a new `Machines/Clean` import), which the facade imports
    (`outputs/merge-order.txt`).
  - #131 (stacked on #130) changes `CodeSimulator.lean`, which the facade also imports.
  - Merge #124 before #130 and #131. If either lands first, re-elaborate #124's facade against
    the post-merge snapshot before merging (1 module).
