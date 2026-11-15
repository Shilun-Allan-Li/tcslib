# Gate 31 · resolutions, round 1 · CLOSED

Codex's verdict is **CLEAR** for the machinery audit: 0 blockers, 0 majors, 1 minor, 0 notes.
- **Findings:** `findings/gate31-prf-long-findings.md`, SHA-256 `89ef7091ed05ad94af57965723c12d4a0cfbdfc21590b94921305abf1f7b242b`.
  Codex's reproduction ZIP was not supplied; the Markdown is the record.
- **Audited head:** `fbd37f447596d4207c8d08b7ef7602f57fe95198`, records `9cc4db62`, exchange `37f16e2b`.

Codex confirmed the following:
- D1–D4 match the 23 drafted signatures, and the 22 old proofs are genuine specializations;
- the frozen statements hold: 126 retained declarations, 38 definition bodies unchanged;
- the B1 consumer map works seed by seed, and the brief's obligations for `sc-garble` are listed;
- there is no undisclosed duplication beyond DL-46;
- seal A passes 6/6 head files and 5/5 base files, strict and coe, with the controls verified;
- the merge with #314 has no interaction.

| # | Severity | Disposition |
|---|---|---|
| G31-01 | minor | **Fixed, records and PR text only.** The review's Rule-10 bullet and F-07, and the PR #315 description, said seal B fails only where the base fails. Both now say that six declarations newly fail B, two of them in `ReductionMachine`, all from `PolyExpr.eval` reductions or their cascades. The pack had disclosed this, and no Lean changes. |

**Erratum 1** (filed after the pin): the pack's 138 downstream-of-both count should be 85 TCSlib and audits modules.

**Gate 31 is CLOSED.** One merge condition remains, and it is not an audit item: the maintainer's integration rebuild
on the tree merged with #314.
