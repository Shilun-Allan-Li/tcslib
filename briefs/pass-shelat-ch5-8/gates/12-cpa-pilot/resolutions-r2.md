# Gate 12 · resolutions, round 2

**Status: CLOSED** (round 2: 0 blockers, 0 majors, 1 minor). Auditor Codex, 2026-11-11; findings
filed verbatim in [findings/](findings/gate12-cpa-pilot-r2-findings.md) (SHA-256
`76d6ceb110f4857c918a07fe23dc4597be0c733170e93cacdff4c82bea8ea76b`). Round-1 findings G12-01–03
verified fixed; the round-1 note (`cap(n) > 0`) verified applied.

| Input | Pin |
|---|---|
| Exchange | `29828d20fdabc6c8f29d1f308dc3312a2496654e` |
| PR #287 Lean head | `80825587f3d6bda7db2b6472fb0cc88e728e73e7` |
| Records | `d1ff29f87becde67d7d992e53da45bcede32f9c0` |

| # | Severity | Resolution |
|---|---|---|
| G12-R2-01 | minor | **Fixed.** The live PR #287 description now distinguishes the two new admissions from the four existing ones in the replay and names the checked head. |

This closes the statement gate; it does not certify the proofs. The fills of `adaptive_cpa` and
`bitwise_padded_cpa` follow, with a proof audit.

**Clear to merge** — #287 at `80825587f3d6bda7db2b6472fb0cc88e728e73e7`.
