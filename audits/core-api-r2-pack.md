# External audit pack — the core specification API (PR #116), round 2

Round 1 (`audits/core-api-pack.md`) returned **FAIL, 0 blockers, 2 majors, 3 minors**
(`audits/core-api-findings.md`, verbatim).
- The maintainer's review verified all five findings at the auditor's severities
  (`audits/evidence/core-api/r2/gate-review.md`).
- The resolutions are in `audits/core-api-resolutions.md`.
- This round checks the repair of findings 1 and 2 and the records fixes of findings 3–5.

**The repair** (`lean/core-api`):
- `f2e0f3d7` applies the review's two patches unchanged
  (`audits/evidence/core-api/r2/repair-required.patch`, `repair-optional.patch`).
- `395771bc` merges the campaign tip.
- `93c4c630` merges PR #112's round 2: the replays are stacked; #112 merges first.
- **No statement or definition changes.**

| Finding | File | Repair |
|---|---|---|
| 1 | `Finite.lean` (campaign-owned; raw-layer section) | `MultiTapeTM.runFrom_with_q₀`: `({ tm with q₀ := q }).runFrom cfg t = tm.runFrom cfg t`; `MultiTapeTM.initCfg_with_q₀`: `({ tm with q₀ := q }).initCfg x = Cfg.init q x` |
| 1 | the U2-S draft (`audits/evidence/drafts/u2s-fill-startup.DRAFT.md`) | the cleaned canonizer is restarted at `.init q₀` and read through `cleanTM_run`; Hydroxyi's `Machines/CleanSweep` (the auditor's proposed home) is not edited |
| 2 | `Finite.lean` | `FinTM.computesFunInTime_iff`; also `computesFunInTimeVia_iff`, `computes_iff` |
| 3 | the bundle | its Lean now comes from the merged head, so the consumers are the tip's (`ZoneRebalance` with #115's helpers, `StepBlockForward` with #114's proof) |
| 4 | `audits/evidence/core-api/logs/axioms.log` | `serializeK_eq`'s print appended |
| 5 | `Configuration.lean`, `Deterministic.lean`, `Finite.lean` (headers) | the vendoring inventories list the added API lemmas and the relocation |

## Brief for the auditor

1. **Finding 1 closed?**
   - The two restart lemmas must be correct and general.
   - The U2-S route must start the cleaned canonizer without unfolding any definition:
     `F' := ⟨_, _, { cleanTM … with q₀ := .init q₀ }, _, _⟩`, then `initCfg_with_q₀`, then
     `cleanTM_run`; the probe is `r2/probes/CleanRestartProbe.lean.txt`.
   - The same device must cover a host composite's start state (the auditor's "also
     inventory").
   - **Constraint:** Hydroxyi's files are cited as is and never edited (`policy.md`; the user's
     standing rule), so a fix inside `Machines/CleanSweep` is not available.
2. **Finding 2 closed?** `computesFunInTime_iff` states exactly the definition, and with
   `computesInTime_iff` it gives the introduction and elimination U2-S's step 1 needs.
3. **Findings 3–5.**
   - The bundled consumers are the merged head's.
   - The axiom log is complete for the hand-written additions.
   - The vendoring headers are accurate.
4. **No behaviour change.** Only theorems and docstrings are added or edited; the freeze shows no
   statement changed.
5. **Evidence.**
   - **Elaboration:** `r2/logs/elab-*.out`.
   - **Axioms:** `logs/axioms.log`, round 2's section.
   - **Copy-text screen:** `r2/logs/screen-{base,repaired}.txt` (three files, 0 new pairs).
   - **Lint check 8:** `r2/logs/lint-*-check8.txt`.
   - **Replay:** `r2/replay-lcapi.log` at the stacked head `93c4c630`: 320 of 320, 0 failed. The
     per-module sorry counts equal a static count of the tree (`r2/replay-lcapi-static.txt`: 0
     mismatches, 94 in total), and on the 85 modules shared with #112's round-2 replay they are
     unchanged.
6. **Records.** Check the resolutions and this pack against the evidence.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`. Findings go verbatim into
`audits/core-api-r2-findings.md`. The gate closes when it has zero blockers and zero majors.
