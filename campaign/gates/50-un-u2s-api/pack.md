# External audit pack — the API for the UN and U2-S continuations (PR #132, an API gate)

Campaign: the Arora-Barak chapters 3-4 plan, C1 (the nondeterministic time hierarchy, [AB09,
Theorem 3.2]) and the `k`-generic universal machine. The user's "Everything" rule (2026-10-16,
`policy.md` §1): every definition a brief's route reads gets a published equation before the
brief is dispatched.
- **Why:** the reviews of two fill deliveries of 2026-10-17 found one gap each, and the user ruled
  on 2026-10-18 that both are published before either continuation issues:
  - **C1-UN** (the universal NDTM, `Diagonalization/NTimeHierarchy`; review
    `campaign/fills/c1/reviews/universal-1/REVIEW.md`, its UN-1): the setup's scratch cleanup
    needs the pair extractor's **halting configuration**; the published `pairExtractTM_fst` gives
    its output only. Gate 47 (note 7) confirmed the gap.
  - **U2-S** (the universal startup, `UniversalK`; review
    `campaign/fills/u2s/reviews/startup-1/REVIEW.md`, its F1): normalizing the phase-2 return
    needs the buffered composite's second-phase fields **at the composite's own tape-index type**;
    the published `simps` fields are stated at `Fin (M₁.k + (1 + M₂.k))`, which a consumer reaches
    there only by unfolding. Gate 48 (note 2) confirmed the gap.
- **The head:** `lean/un-u2s-api` at `91154701`: one commit `d3b70b3e` (the API, on the campaign
  branch of 2026-10-18 before #124), then a merge of the campaign branch after #131
  (`0bf4f085`). Its Lean diff from the tip is exactly the two files below.

| File | Additions |
|---|---|
| `TuringMachine/Build/Primitives` | `FinTM.pairExtractTM_fst_run`: on `pairEncode a b`, the extractor `pairExtractTM true false` first halts after exactly `4·|a| + 5` steps, in the whole configuration (output `a`, input head at `2·|a| + 3`, its work tape `bufferTape a` with the head at `|a|`), live before. `FinTM.pairExtractTM_fst_run_budget`: the same at the published budget `5·(|z| + 1)`. Two private helpers (`extractCfg_congr`, `extract_scan`). The module's Contents line names the two. |
| `TuringMachine/Simulation` | `FinTM.bufferedSecondCfg_workTapes_cast` and `_workTapePos_cast` (`rfl`): the second phase's fields at an index `i : Fin (bufferedCompTM M₁ M₂).k`, read as the block layout at `Fin.cast (bufferedCompTM_k M₁ M₂) i`. |

- **Evidence:** `evidence/`: the two modules' elaborations with axioms; the freezes; the lint;
  the patch; the replay script, list, log and static check; the PR body.
- **The reviews' probes** (the motivating evidence): the UN review's draft use of the extractor
  lemma (`campaign/fills/c1/reviews/universal-1/UN1-pairExtract-draft.lean.txt`), and the U2-S
  review's phase-2 transport, sealed and unsealed (`campaign/fills/u2s/reviews/startup-1/38-…`,
  `39-…`).
- **The bundle** contains the two touched files at the head; their consumers' current state
  (`Diagonalization/NTimeHierarchy`, `UniversalK`); the two reviews and their probes.

## Brief for the auditor

1. **Faithfulness.**
   - `pairExtractTM_fst_run`: is the exact time `4·|a| + 5` right (the aligned scan `2·|a|`, the
     separator block `2`, the rewind and replay `(|a| + 1) + (|a| + 1)`, one halting step)? Is the
     endpoint exactly the configuration stated, every field, including the work tape and its
     head, for every `a` (including `a = []`) and every suffix `b`? Is the liveness clause right?
   - `pairExtractTM_fst_run_budget`: does `4·|a| + 5 ≤ 5·(|pairEncode a b| + 1)` hold, and does
     the corollary follow from the halted configuration's absorption?
   - The cast pair: do the two `rfl` equations state the definition's behaviour at the
     composite's index type, with the right block layout (`tapeBlocks tapes (bufferTape y)
     c.workTapes` and `tapeBlocks heads (inputPos − 1) c.workTapePos`)?
2. **Sufficiency.** Does the extractor lemma close UN-1 (the UN review's draft), and does the cast
   pair let U2-S's phase-2 normalization rewrite without unfolding (the U2-S review's sealed probe
   fails with the old fields and passes with the new)?
3. **Rule 10 in the API's own proofs** (disclosed): `pairExtractTM_fst_run`'s proof reads its own
   file's `pairExtractTM` and `extractCfg` by unfolding, which is allowed; but its `hinit` step
   also unfolds `MultiTapeTM.initCfg` and `Cfg.init` through `simp`, where `initCfg_eq` and the
   `Cfg.init_*` field lemmas are published, and `hlast` unfolds `MultiTapeTM.step` and
   `Action.apply` for this file's own machine. The fill rule 10 forbids the first kind for fill
   workers. Should the maintainer's API proofs meet it too (a follow-up commit re-pointing `hinit`),
   or is it acceptable here?
4. **Public-facing text:** the four docstrings and the Contents line carry no campaign labels.
5. **No collateral change:** the freeze shows additions only (`Primitives` 47 → 49 publics,
   234 → 236 privates; `Simulation` 60 → 62 publics), no `@[simp]` attribute, and no statement
   changed.

## Repository-side attestations (verify or challenge)

- **Elaboration** (maintainer, against `oleans-lx2b`): both modules, 0 errors; no warning from
  the new lines; `Primitives`' existing linter notes unchanged. **Axioms:** the four new names
  use `[propext, Classical.choice, Quot.sound]`.
- **Lint:** `TuringMachine/` 0 FAIL, 63 WARN.
- **Elaboration evidence:** `evidence/elab-*-axioms.out` (each module at the head with the new
  names' `#print axioms` appended); the freezes `evidence/freeze-*.txt`; the patch
  `evidence/api.patch`.
- **Replay:** `replay-l132.sh`, 314 modules (the downstream closure of `Build/Primitives` and
  `Simulation` on the merged tree, which contains every module #124 and #129–#131 changed),
  chained from `oleans-lc6m` (#131's replay at the merged state). **Passed (user, 2026-10-18):**
  314 of 314 at `91154701`, 0 failed, static-equal (93) (`evidence/replay-l132.*`,
  `evidence/down-l132.txt`).

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `campaign/standards/TEMPLATE.md`. Findings go verbatim into
`campaign/gates/50-un-u2s-api/findings.md`. The gate closes when it has zero blockers and zero
majors.

**Deliver your findings as a downloadable Markdown file named `un-u2s-api-findings.md`** (the
findings table and the verdict line, no other wrapping), and also paste its content in your reply.
