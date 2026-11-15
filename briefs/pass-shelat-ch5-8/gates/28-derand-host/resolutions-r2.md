# Gate 28 · resolutions, round 2 · CLOSED

Codex's verdict is **CLEAR**: 0 blockers, 0 majors, 2 minors, 1 note. All four round-1 findings are closed.

- **Findings:** `findings-r2/gate28-derand-host-r2-findings.md`.
- **Audited head:** `0c04d1eb1e5450372632a23f3e94f3b7bfc37606`.
- **Pins:** records `50416ccc67b9a28fea74177c2cb2ecf562cc6b29`, exchange `4bf496ccd5ffa48f70704251cd0310d8aa13a2fe`.

| # | Round 1 | Round 2 |
|---|---|---|
| G28-01 | major | **Closed.** H17 is in the canonical registry and matches the code. |
| G28-02 | major | **Closed.** One machine carries both `DecidesInTime S B` and the head envelope, with the same budget. Codex proved the envelope from the time bound: `\|p(v)\| ≤ min(v, b)`. No admitted space spec is used. |
| G28-03 | minor | **Closed.** |
| N28-01 | note | **Closed for this gate.** The derand brief update is the recorded next action. |

| # | Severity | Disposition |
|---|---|---|
| G28-R2-01 | minor | **Fixed.** The PR #312 description is rewritten for the final head: the machine contract `exists_seedMajorityTM`, the corollary admitted until `mem_DTIME_iff`, the proved reader, the two intended admissions, and the round-2b evidence. |
| G28-R2-02 | minor | **Erratum to `pack-r2.md`.** The pack said both PRs are imported by both root `TCSlib` and `audits/pass-shelat/Checks`. In fact root `TCSlib` is the only common importer: `Checks` reaches #312 but not #311. The conclusion is unchanged. The pack is pinned, so the correction is recorded here. |
| N28-R2-01 | note | **Ruling (Seyoon, 2026-11-15): pre-approved.** The derand fill may add exactly one `FinTM.decidesInTime_iff` reader beside `DecidesInTime` in `Complexity/ClassP/DTIME.lean`. It is proved by `Iff.rfl`, has a formula docstring and no attribute, and sits next to the already approved `mem_DTIME_iff`. It is the third named scope exception, with the `computesFunInTime_find` harvest and `mem_DTIME_iff`. |

**Combined tree.** Codex does not require a combined-tree build for this statement gate. #311 does not import the
changed layer, and the only common downstream module is the unchanged root facade.

## Disposition
**PR [#312](https://github.com/Shilun-Allan-Li/tcslib/pull/312) is marked ready at `0c04d1eb`.** It is a statement PR, and the host
contract and corollary stay admitted for the `derand` fill.

Before `derand` is dispatched, its brief is reissued (`issued-r2`) with:
- step 4 and checkpoint 1 consuming H17;
- the three pre-approvals;
- regenerated order and roots, since the closure gains `Randomized/SeedMajority`;
- Codex's route notes: binary fuel, the terminal-step invariant, and the direct time bound in place of the
  polynomial-fuel `final_bound`.
