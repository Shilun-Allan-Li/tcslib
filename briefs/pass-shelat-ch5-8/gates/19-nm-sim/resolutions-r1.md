# Gate 19 · resolutions (round 1)

**Status: CLOSED.** The Codex audit returned CLEAR: 0 blockers, 0 majors, 1 minor, 0 notes.

- **Findings:** filed verbatim as `findings/gate19-nm-sim-findings.md`, SHA-256
  `4a15f3a8bf7dab6eab1e2f437d75770e3fcc8dde7d0b5957ee4d3f080f33137c`.
- **Not received:** the companion ZIP the report mentions. It is not needed for closure.
- **Audited head:** `5da558b4d97aca00efd6dc396a1b0f3bffff268b`. Records `40213c18`, exchange `d17ee1ca`.

| # | Severity | Finding | Resolution |
|---|---|---|---|
| G19-01 | minor | The `Simulation/IndSim.lean` module docstring has no `## Main definitions` section (policy §1, file header). | **Fixed** in `dcb8941c6573358e31dd096b153415d12b42d357` (5 docstring lines). The section says the module defines nothing and points to where `nmParams` (`Reduction.lean`) and `recDist` (`Recover.lean`) are defined. The other 10 files already had the section. |

**After the fix:**
- **Rebuild:** `IndSim`, the owned file, the 3 facades and root `TCSlib` were rebuilt on the full-library tree, all rc 0 with 0 warnings. Each row is bound to the head's source hash (`landing-r1/`).
- **Axioms:** both targets, `simNMSecure_cpa_iff_nmSecure_cpa` and `exists_nmAdversary` print
  `[propext, Classical.choice, Quot.sound]`.
- **Scope of the change:** comment only. No statement, proof, import or name changed, so the Rule-10 seals and the
  statement census from the audit carry over unchanged. The longest line is exactly 100 characters.

**PR #297 head:** `dcb8941c6573358e31dd096b153415d12b42d357`. It is marked ready for review.
