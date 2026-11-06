# Fill report: unit rsa (`TCSlib/Cryptography/Candidates/RSA.lean`)

**Status: checkpoint (work in progress).** The final report replaces this file.

- Base: `16a7d02d69cae1a700c131e3cc3dd918a7b3d6e1` (`git rev-parse`). Local branch `fill/rsa`, never pushed, never rebased.
- Ran as an internal worker under `issue/internal-env.md` (no preflight floor, cache or bootstrap step).
  Machine at start: `nproc` 4, MemTotal 16.5 GB, MemAvailable 14.9 GB (`evidence/logs/preflight.log`).
- Module check times: `evidence/logs/module-checks.log`.

## Targets (brief order)

| # | Target | State |
|---|---|---|
| 1 | `rsaSampler_spec` | filled |
| 2 | `statClose_sampleUnitL` (S3) | filled |
| 3 | `rsaCollection_sampleClose` | filled |
| 4 | `polyTimeComputable_unitSampleStr` | filled |
| 5 | `polyTimeComputable_rsaGenRaw` | filled |
| 6 | `polyTimeComputable_rsaFromFactorRaw` | filled |
| 7 | `rsaCollection_invProbAt_le` | open |
| 8 | `factorProb_le_rsaProb` | open |
| 9 | `rsaCollection_oneWay`, `rsa_imp_factoring` | open |
