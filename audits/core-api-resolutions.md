# The core specification API gate (PR #116): resolutions

**Gate:** PR #116, the core specification API, with the zone layer.
- Pack: `audits/core-api-pack.md`.
- Round 1 bundle SHA-256: `fc8219a63b5c818d5ed4937221cabc18aa10b43b99f77f95b238f93798f078e5`
  (63 sections; folder `infra_local/gate-dispatches/30-core-api-gate/`).

## Round 1

The findings are in `audits/core-api-findings.md`, verbatim. **FAIL: 0 blockers, 2 majors,
3 minors, 0 notes.** The auditor did not run Lean. It found the 45 generated and 46 explicit
equations faithful and the case families exhaustive.

The maintainer's review sub-agent verified every finding against the source at `d5255232`
(`audits/evidence/core-api/r2/gate-review.md`). All five are true, at the auditor's severities.

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 1 | major | `cleanTM`'s initial state has no published equation, so U2-S's cleaned canonizer cannot be started without unfolding `cleanTM`. | `Machines/CleanSweep.lean` is Hydroxyi's (his header, his only commit `f70c57c2`), so the proposed fix there is not available. No public statement of his gives `(cleanTM M q).q₀`.<br>**Fixed in round 2 by a generic restart:** `MultiTapeTM.runFrom_with_q₀` and `MultiTapeTM.initCfg_with_q₀` (`Finite.lean`, campaign-owned, both `rfl`). `{ tm with q₀ := q }` runs as `tm` does, from `Cfg.init q`.<br>U2-S restarts the cleaned canonizer at `.init q₀`, the device of his own `cleanTM_run` proof, and reads it through `cleanTM_run` alone (probe `r2/probes/CleanRestartProbe.lean.txt`, 0 errors). The same device serves a host composite `R`, whose `q₀` also has no equation (the auditor's "also inventory"). The U2-S draft's step 1, lemma list and pitfall are updated. |
| 2 | major | `FinTM.ComputesFunInTime` has no characterization or general introduction. | **Fixed in round 2:** `FinTM.computesFunInTime_iff` (`Iff.rfl`), beside the definition. With it come `computesFunInTimeVia_iff` and `computes_iff`, so all of `Finite.lean`'s definitions are covered (lint check 8). |
| 3 | minor | The bundle's consumer files predate #114 and #115 (`ZoneRebalance` 331 lines; `StepBlockForward` the 132-line skeleton). | **True; a bundling error.** Every `TCSlib/` path was taken from `d5255232`, which predates the merges. The other consumers (`UniversalK`, `InputDevice`, `UniversalStartup`, `WindowRun`, `Clean`) equal the tip.<br>**Fixed:** the head now merges the tip, and round 2's bundle takes its Lean from the merged head. The replay elaborates the actual citers, including `StepBlockForward`'s proof, which cites the moved lemma. |
| 4 | minor | `serializeK_eq` is missing from `axioms.log`. | **Fixed:** appended, `[propext, Quot.sound]` (measured by the review, `r2/logs/elab-CodeSimAx.out`). |
| 5 | minor | The vendoring headers of `Configuration` and `Deterministic` omit this PR's additions. | **Fixed in round 2:** both headers list the added API lemmas and the relocation, separated from the upstream content. They also list two earlier unlisted changes, the September re-proofs and D6's `timed_input_bound`. `Finite.lean`'s sentences calling the vendored files "unmodified" or "byte-comparable" are reworded. |

**Carried to U2-S's brief (the auditor's route answer):** the rewind's exact time comes from the
published `rewind_scan` and `controlAction_apply`. `FinTM.timed_rewind`'s existential bound
alone is insufficient.

## Round 2

- **The repair:** `lean/core-api`.
  - `f2e0f3d7` applies the review's two patches unchanged. It adds 5 theorems and edits the
    vendoring headers. No statement or definition changes.
  - `395771bc` merges the campaign tip (#113, #114, #115).
  - `93c4c630` merges #112's round 2: the replays are stacked and chained, as for #112 and #113.
    **#112 merges first.**
- **Tested by the review** against `oleans-lf3p`:
  - elaboration: 0 errors, with warning counts as at the base (Finite 2, Configuration 3,
    Deterministic 0);
  - freeze: only the 5 theorems added;
  - lint check 8: Finite's line goes, nothing new;
  - copy-text screen of the three touched files: 50 declarations, 10 pairs, 0 new.
- **Replay:** `replay-lcapi.sh` covers the eleven changed modules' downstream closure at the stacked
  head (320 modules), from `oleans-lapi2`, the tip plus #112. The user runs it.
- **Round-2 gate:** a short check of findings 1 and 2's repair, with the replay log and the
  merged-head consumers. Pack: `audits/core-api-r2-pack.md`.
