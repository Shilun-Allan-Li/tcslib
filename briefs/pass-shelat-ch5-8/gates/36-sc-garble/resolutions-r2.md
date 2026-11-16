# Gate 36 · resolutions, round 2 · CLOSED

Codex: **CLEAR**, 0/0/1/0.
- **Findings:** `findings-r2/gate36-sc-garble-r2-findings.md`, SHA-256 `aeae1517610048e6447bb71b49db08531c48f4637ffc286f731747ae42318ba1`.
- **Audited:** head `8c3f3e3fe2912784f680c10f8c478d2eeeeb7f6a`, records `298338e3`, exchange `0bdffba7`.

| # | Severity | Disposition |
|---|---|---|
| G36-01 (r1) | major | **Closed.** LE-gate36 removes the duplicate, re-points the use to the public `length_le_length_encodeList`, and adds an import that creates no cycle. |
| G36-02 | minor | **Fixed by erratum** (`erratum-r2-1.md`). The paired-control summaries in `pack-r2.md` and `landing-r1/PROVENANCE.txt` overstated the sealed negatives. The correct counts are **coe 5** (A 2, B 3) and **strict 7** (A 3, B 4). Strict also has **2** disclosed `ctlCoeReader` positive-reader failures, so its 9 diagnostics break down as 7 + 2. The raw evidence is preserved and unchanged. |

What else Codex confirmed:
- `merge-tree(654323f2, 8c3f3e3f)` is exactly the built tree `5662520d`.
- 392/392 modules build.
- decls2 shows exactly 1 REMOVED since round 1, and the frozen check finds 0 differences.
- The seals pass.
- The axioms are standard, and admissions go 215 → 208.
- The trial merge with #324 reproduces.
- A mechanical cross-check against 20,735 theorems found no new duplicate.

**Gate 36 is CLOSED.** One merge condition remains: the combined build of all open PRs.
