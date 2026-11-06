# Fill dl-a: REPORT (checkpoint 2: all targets filled; final checks running)

Unit **dl-a** of the brief `briefs/pass-shelat-ch5-8/fills/dl-candidates/brief-issued.md`.
Owned files: `TCSlib/Cryptography/Candidates/Concrete.lean`, `TCSlib/Cryptography/Candidates/DiscreteLog.lean`.

- Base: `16a7d02d69cae1a700c131e3cc3dd918a7b3d6e1` (local branch `fill/dl-a`, never pushed).
- Ran as an **internal worker** under the maintainer's environment note (no preflight, no cache
  step; `.lake/packages` linked to the populated Mathlib tree; olean tree `fill-dl-a-oleans`).
  `nproc` 4; memory at start: 16.9 GB total, 16.1 GB available (`free -b`, see
  `evidence/logs/start-resources.log`).

## Targets (status at this checkpoint)

| # | Target | Status |
|---|---|---|
| 1 | `statClose_rejectBlocksL` (Concrete) | filled |
| 2 | `statClose_sampleBelowL` | filled |
| 3 | `polyTimeComputable_expSampleRaw` | filled |
| 4 | `expSampler_spec` | filled |
| 5 | `expCollection_sampleClose` | filled |
| 6 | `expCollection_invProbAt_le` | filled |
| 7 | `expCollection_oneWay` | filled |

Module checks: `evidence/logs/module-checks.log`. Final sweep, axioms, seal and lint at the final delivery.
