# The specification API gate (PR #112): resolutions

**Gate:** PR #112, the specification API: the contract combinators' and row contracts' field
equations, and the layout and record facts.
- Pack: `audits/spec-api-pack.md`.
- Round 1 bundle SHA-256: `91f96cf5fea0a6d2f07040ebeaeb423362dc26a298dad58e5c53beda5a19dca1`
  (52 sections; folder `infra_local/gate-dispatches/29-spec-api-gate/`).

## Round 1

The findings are in `audits/spec-api-findings.md`, verbatim. **FAIL: 0 blockers, 2 majors,
2 minors, 1 note.** The auditor did not run Lean.

The maintainer's review sub-agent verified every finding against the source at `28824c36`
(`audits/evidence/spec-api/r2/gate-review.md`). All five are true. Finding 2 is downgraded to
minor: a published route already reads the mapped sweeps' cells at admissible starts, and the
probe for it elaborates.

| # | Severity (auditor → review) | Finding | Resolution |
|---|---|---|---|
| 1 | major → major | `ReturnContract.release`, `RoundContract.release` and `Contract.ofSegment` have no field equations. G4's binding iteration hosts read them. | **Fixed in round 2:** `attribute [simps (config := { isSimp := false }) pre time post lo hi]` on the three definitions, in their modules (`Contract/Seam`, `Contract/Basic`). That gives 15 equations. |
| 2 | major → minor | No published equation exposes `sweepMapWrite`'s values. | **Fixed in round 2:** `sweepMapWrite_apply` (`rfl`), plus the endpoint cells `copyMapTM_contract_post_workTapes` and `transferMapTM_contract_post_workTapes`. The cells were already readable through the contract's `run` field and `copyMapTM_run_ofCfg` (probe `r2/probes/ApiRunRoute.lean.txt`). |
| 3 | minor | WindowClock's appendix still grants the superseded 2026-10-15 unfolding permission. | **Fixed in round 2:** the paragraph names `recordLength_eq`, `record_pos_lt` and `recordAt_iff`, and marks the ruling of 2026-10-16 as superseding the permission. The line count is unchanged, so the F3 continuation draft's line references hold. |
| 4 | minor | `recordAt_iff`'s and `recordLength_eq`'s docstrings are bare labels. | **Fixed in round 2:** both state their mathematics (the interval and the layout equality; the length formula and its parts). |
| 5 | note | The bundle has no completed replay log. | **Resolved:** `replay-lapi.log` ran at exactly `28824c36`, 89 of 89 modules, 0 failed. It finished after the bundle was built. Round 2 has its own replay (`replay-lapi2.sh`, 85 modules), and its log goes into the round-2 bundle. |

**The auditor's further interfaces** (if a continuation chooses them): `Contract.mapState`,
`Contract.lockstep`, `RoundContract.returning`, `RoundContract.escaping`,
`ReturnContract.toRound`.
- No drafted route reads them.
- **Taken anyway** in round 2: the same attribute, 25 equations. `Contract/Basic` is edited and
  replayed in any case, and the rule adopted the same day ("definitions land with their
  lemmas", `policy.md` §1) asks for them.
- `mapState`'s attribute line sits with `Contract.lockstep`'s, after that definition. Placed
  directly after `mapState`, it raised a pre-existing near-half overlap with `branch` to a 51%
  pair in the copy-text screen.

**Related (not a finding).** `Turing.Round` and `Turing.Segment` are Prop-valued definitions
without `_iff` lemmas. G4's routes need neither unfolded: rounds come from `RoundContract.round`
or `Round.of_cut`, and segments are passed whole to `ofSegment`. This is checked again at the
G4 continuation's pre-ship inventory.

**The numeric claims** all check out: 52 sections; 85 equations (5 + 15 + 65); the patch
reversal; the screen at 711 → 712 declarations, 350 pairs and 116,080 characters.

## Round 2

- **The repair:** `lean/spec-api` at `52965dc9`, the review's two patches applied unchanged
  (`r2/repair-required.patch`, `r2/repair-optional.patch`). The campaign tip is then merged in at
  `caa93c12`, with #114 and #115, so that the replay covers what lands.
  - It adds 3 theorems and 40 generated equations, and edits 3 docstrings plus the "Main
    results" lists. No statement or definition changes.
- **Tested by the review** against `oleans-lapi`:
  - all six repaired files elaborate with 0 errors, with warning counts as at the base;
  - the freeze shows no statement changed and nothing removed;
  - the lint shows 0 FAIL, with the WARN sets unchanged;
  - the copy-text screen of the six-file population gives 714 declarations, 350 pairs, 0 new.
- **Replay:** `replay-lapi2.sh` covers the six files' downstream closure at the merged tree
  (85 modules), from `oleans-lg4p`, the campaign tip plus round 1. **Passed (user, 2026-10-16):**
  85 of 85, 0 failed (`r2/replay-lapi2.log`). The sorry counts equal round 1's, except
  `StepBlockForward`, 1 → 0 (#114's H2-F).
- **Round-2 gate:** a short check of the repair diff (finding 1 is the remaining major), with the
  replay log. Pack: `audits/spec-api-r2-pack.md`.
