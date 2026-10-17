# Review of the round-2 gate audit of PR #116 (the core specification API)

**Verdict: the gate can close.** The audit returned PASS, 0 blockers, 0 majors, 0 minors and
0 notes, and I confirm it.

**Factual claims.** Every one I checked holds. That includes the two the auditor marked as
maintainer attestations:
- I re-ran the whole-tree static sorry comparison myself: 320 modules, 0 mismatches, 94.
- I recomputed the replay closure myself: graph2 gives the same 320 modules.

**Findings 1 and 2 are closed under the no-unfolding rule.**
- The auditor's evidence for the restart route used stand-in lemmas. I added a probe against
  the replayed head (`oleans-lcapi`) that uses the **published**
  `MultiTapeTM.initCfg_with_q₀`, `runFrom_with_q₀`, `FinTM.computesFunInTime_iff` and
  `computesInTime_iff`.
- It derives `ComputesFunInTime` for the restarted cleaned machine, bundled as a `FinTM`, from
  `cleanTM_run`: 0 errors, 0 warnings, exit 0. `cleanTM` is never unfolded.

**The bundled consumers are the merged head's.**

## Inputs checked

- **Audit text:** `audits/core-api-r2-findings.md` (untracked), read as data.
- **PR head:** `origin/lean/core-api` = `93c4c6304198dcb9147ed655ebcd7cb940c6a4b6`.
  - Parents: `395771bc` (which itself merges `f2e0f3d7` with tip `eaedd234`) and `caa93c12` (#112 round 2).
  - `f2e0f3d7`'s three files are blob-identical to my repaired copies: `Finite` `c9234021`, `Deterministic` `5b3f881e`, `Configuration` `b40d0eab`.
- **Campaign tip:** `bb4c46dc`, which contains #112 (`caa93c12` is an ancestor).
  - `git diff --name-only bb4c46dc 93c4c630 -- '*.lean'` lists exactly #116's eleven files.
  - Nothing under `SpaceComplexity/Machines/` (Hydroxyi's `Clean`, `CleanSweep`) differs.
- **Bundle:** `infra_local/gate-dispatches/32-core-api-r2-gate/core-api-r2-bundle.md`, SHA-256 `559c64bb…592b`, as commissioned.
  - 89 sections with 0 duplicate paths; `BUNDLE-FILES.txt` has 89 entries.
  - `mkbundle-mixed.py … --verify` with the README's revisions (Lean `93c4c630`, other `179db5b3`) gives `verified 89 segments`.
- **Evidence:** extracted from the tip with `git archive` into `review/core-api-r2-gate/ev/`.
- **Worktrees** (detached, clean after testing): `review/core-api-r2-gate/wt-head` (`93c4c630`) and `wt-tip` (`bb4c46dc`).

## The audit's claims

| Claim | My check | Result |
|---|---|---|
| Hash; 89 unique sections | `shasum`; header count | correct |
| The restart pair at `Finite.lean:232`, `:239` | `git show 93c4c630:…Finite.lean` | correct; the three iffs at 287, 304, 323 |
| Both U2-S draft copies carry the repaired construction and cite the pair | both drafts (byte-identical) | step 1 (lines 166–173) builds `{ cleanTM E.canonizer.tm E.canonizer.tm.q₀ with q₀ := .init E.canonizer.tm.q₀ }` and proves `ComputesFunInTime` through `computesFunInTime_iff`/`computesInTime_iff`; pitfall 359–362 and the inventory (77, 80) cite the pair |
| `CleanRestartProbe` uses stand-ins and logs exit 0; `FiniteAx` = repaired `Finite` + appended commands | r2 probes and logs | the probe is byte-identical to my round-1 probe; `elab-CleanRestartProbe.out` exit 0, no diagnostics. `FiniteAx.lean.txt`'s first 459 lines equal the head's `Finite.lean`; then 5 `#check` + 5 `#print axioms` |
| Repair patches as reviewed; reversal blobs `52aa83c`/`b609dc9`/`2a0820d` → `c923402`/`5b3f881`/`b40d0ea` | `cmp` with my patches; blob ids | byte-identical; the repaired blobs equal the head's |
| No existing code changed by the repair; 5 theorems added | my round-1 freeze run on the same files | `STATEMENT CHANGED: []`, no body change |
| Consumers: `StepBlockForward` 555 lines `60e29249` (proved; cites `visitedByTapeHead_add_subset` at 525); `ZoneRebalance` 571 lines `9deb85fb`, 18 privates | blob ids at head and tip | correct. Bundled = head = tip for all eight consumer and context files (`UniversalK`, `InputDevice`, `UniversalStartup`, `StepBlockForward`, `WindowRun`, `ZoneRebalance`, `Clean`, `CleanSweep`) |
| `axioms.log`: 51 distinct names, 52 prints (`zoneCapacity_eq` twice); `serializeK_eq` `[propext, Quot.sound]`; no `sorryAx` | parsed the log | correct |
| Elaboration logs: exit 0; Finite 2 warnings before and after, Configuration 3, Deterministic 0; probe silent | r2 logs (my round-1 runs) | correct |
| Screen: 50 declarations, 10 pairs, 728 characters, before and after | r2 screen logs | correct; byte-identical to my round-1 screens |
| Lint check 8: 71 → 70 WARN, 0 FAIL; only Finite's three names removed | r2 lint logs (my runs) | correct |
| Replay: 320 distinct rows in the supplied order, all exit 0 / 0 errors, sorry sum 94; both consumers present | `replay-lcapi.log` (== evidence copy) | header `replay-lcapi at 93c4c630 … (320 modules)`, `# modules=320 failed=0`. The order equals `replay-order.txt`. `StepBlockForward sorry=0`, `ZoneRebalance sorry=2`, `Finite`/`Clean` 0. The script prechecks HEAD = `origin/lean/core-api`, a clean tree, `caa93c12` as an ancestor, and #112 round 2's replay |
| 19 included sources agree with their replay rows (12 admissions) | — | consistent with the whole-tree check below |

**The two items the auditor left as attestations, now reproduced:**
- **Whole-tree static sorry comparison.** `r2/staticsorry.py` (read first; read-only) on
  `wt-head` against `replay-lcapi.log` gives `modules 320, mismatches 0, static total 94`.
- **The unchanged counts on #112's 85 modules.** Joining `replay-lapi2.log` with
  `replay-lcapi.log`: all 85 are present in the 320, with identical sorry counts.
- **The closure itself.** graph2 over tip `bb4c46dc`, with the head's eleven changed files
  landed, gives a 320-module downstream closure whose set equals `replay-order.txt`.

## Findings 1 and 2 under the no-unfolding rule

My probe is `review/core-api-r2-gate/RestartPublishedProbe.lean.txt`, output `out/RestartPublishedProbe.out`. It imports only `Machines.Clean`; against `oleans-lcapi` at `93c4c630` it gives 0 errors, 0 warnings, exit 0.

- It defines the U2-S step-1 bundle as the probe's own definition: `probeClean M q : FinTM Bool` with `tm := { cleanTM M q with q₀ := .init q }`, plus its own `rfl` equation.
- From per-input facts about `M`, a per-input time bound `τ`, and `cleanTM_run`, it proves `(probeClean M q).ComputesFunInTime f τ`.
- It uses only `FinTM.computesFunInTime_iff`, `FinTM.computesInTime_iff`, `MultiTapeTM.initCfg_with_q₀`, `MultiTapeTM.runFrom_with_q₀` and `ComputesInTime.mono`. All are published.
- No definition of another file is unfolded, Hydroxyi's `cleanTM` included.

This removes the auditor's remaining caveat that the route probe used stand-ins. Together with
the `FiniteAx` axiom prints, both findings are closed under the rule as U2-S's route needs.

The probe leaves one consumer obligation explicit: the per-input bound `τ` over each length,
which the draft's `Finset.sup` pitfall covers. That belongs to the U2-S fill, not to this API.

## Can the gate close?

**Yes.** Round 2 has 0 blockers, 0 majors, 0 minors and 0 notes, and every round-1 finding is closed:
- findings 1 and 2: the API, the draft and the probes, verified above;
- finding 3: the consumers at the merged head;
- finding 4: the axiom log;
- finding 5: the headers.

The merged head is replayed (320/320, 0 failed). Its static admission count reproduces, and
#112's 85 modules carry unchanged counts. #112 is already merged, so the required order
(#112 before #116) holds.

Optionally, copy `RestartPublishedProbe.lean.txt` and its `.out` into
`audits/evidence/core-api/r2/` as the published-lemma counterpart of `CleanRestartProbe`. No
Lean change is involved.
