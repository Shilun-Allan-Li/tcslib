# Fill report: unit fac (`TCSlib/Cryptography/Candidates/Factoring.lean`)

**Status: checkpoint (in progress).** Internal worker under the environment note
`issue/internal-env.md` (no preflight floors, cache or bootstrap step; worktree and olean tree
provided). Base: `16a7d02d69cae1a700c131e3cc3dd918a7b3d6e1` (`git rev-parse`), branch `fill/fac`.
Machine at start: `nproc` 4, MemTotal 16 GB, MemAvailable 15.5 GB (`evidence/logs/preflight.log`).

## Targets

| # | Target | State |
|---|---|---|
| 1 | `statClose_samplePrimeL_pair` (S2) | filled |
| 2 | `factoringCollection_sampleClose` | filled |
| 3 | `polyTimeComputable_samplePrimeL` (S1) | filled |
| 4 | `polyTimeComputable_samplePairRaw` | filled |
| 5 | `fmult_easy` | filled |
| 6 | `exists_plantFactorer` | open |
| 7 | `factoringCollection_invProbAt_le` | open |
| 8 | `factoringCollection_oneWay`, `fmult_weakOneWay`, `fmult_prod_strongOneWay` | open |

Module checks: `evidence/logs/module-checks.log`.
