# External audit pack — the specification API (PR #112), round 2

Round 1 (`audits/spec-api-pack.md`) returned **FAIL, 0 blockers, 2 majors, 2 minors, 1 note**
(`audits/spec-api-findings.md`, verbatim).
- The maintainer's review verified every finding at `28824c36` and downgraded finding 2 to minor
  (`audits/evidence/spec-api/r2/gate-review.md`).
- The resolutions are in `audits/spec-api-resolutions.md`.
- This round checks the repair. It is short: finding 1 is the remaining major.

**The repair** (`lean/spec-api`):
- `52965dc9` applies the review's two patches unchanged (`audits/evidence/spec-api/r2/repair-required.patch`,
  `repair-optional.patch`).
- `caa93c12` merges the campaign tip (#113, #114, #115) so that the replay covers what lands.
- **No statement or definition changes.**

| Finding | File | Repair |
|---|---|---|
| 1 | `Build/Contract/Seam.lean` | `attribute [simps (config := { isSimp := false }) pre time post lo hi] ReturnContract.release RoundContract.release` |
| 1 | `Build/Contract/Basic.lean` | the same attribute on `ofSegment` |
| 2 | `Build/Contract/Catalog.lean` | `sweepMapWrite_apply` (`rfl`); `copyMapTM_contract_post_workTapes`, `transferMapTM_contract_post_workTapes` |
| 3 | `SpaceComplexity/WindowClock.lean` | the appendix names the API lemmas and marks the earlier permission superseded (docstring only, same line count) |
| 4 | `Build/CfgRecord.lean`, `Build/RecordTable.lean` | `recordAt_iff`'s and `recordLength_eq`'s docstrings state their mathematics |
| further interfaces | `Build/Contract/Basic.lean` | the same attribute on `RoundContract.returning`/`escaping`, `ReturnContract.toRound`, `Contract.mapState`, `Contract.lockstep` (25 equations); `mapState`'s line placed with `lockstep`'s (see the resolutions) |

## Brief for the auditor

1. **Finding 1 closed?**
   - The 15 generated equations of the two release adapters and `ofSegment` must state exactly
     their fields (printed in `r2/logs/probe-ApiSeam.out`, `probe-ApiBasic.out`).
   - Check that G4's binding hosts (`briefs/s13d-fill-g4.md`, "Binding hosts":
     `Turing.Round.iterate`, `Turing.RoundContract.release`) can now be applied without unfolding
     a definition.
2. **Finding 2.**
   - `sweepMapWrite_apply` restates the definition.
   - The two endpoint-cell lemmas are correct and complete (every cell; `src` and `dst` aliasing
     excluded by `hne`).
   - The review's alternative route (`r2/probes/ApiRunRoute.lean.txt`) is sound.
3. **Findings 3 and 4.** The new texts are accurate and state the mathematics (`policy.md` §2).
4. **The 25 further equations.** They must be faithful (`r2/logs/probe-ApiBasic.out`).
5. **No behaviour change.**
   - Only declarations and docstrings are added or edited.
   - `isSimp := false` throughout; no `@[simp]`.
   - The freeze shows no statement changed.
6. **Evidence.**
   - **Elaboration:** `r2/logs/elab-*-repaired.out`.
   - **Copy-text screen** (six-file population, 714 declarations, 350 pairs, 0 new):
     `r2/logs/screen-required+optional.txt` against round 1's `logs/screen-head.txt`.
   - **Lint:** check 8 of the rule *definitions land with their lemmas* (`policy.md` §1,
     adopted 2026-10-16) adds no name, and 17 leave it (`r2/logs/lint-{tip,head}-check8.txt`).
   - **Replay:** `r2/replay-lapi2.log` at the merged head `caa93c12`: 85 of 85 modules, 0 failed.
     Per-module sorry counts equal round 1's replay (`logs/../replay-lapi.log` evidence:
     89 modules, 0 failed) on every common module. The one exception is
     `Build/StepBlockForward`, 1 → 0: H2-F, proved by #114, merged in.
7. **Records.** Check the resolutions and this pack against the evidence.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`. Findings go verbatim into
`audits/spec-api-r2-findings.md`. The gate closes when it has zero blockers and zero majors.
