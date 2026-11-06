# Fill col-b (the `col_zk` ladder): REPORT (checkpoint 1, in progress)

- Base: `16a7d02d69cae1a700c131e3cc3dd918a7b3d6e1` (issue commit, head of PR #210). Local branch `fill/col-b`, never pushed.
- Ran as an **internal worker** under the environment note `issue/internal-env.md` (no preflight, no cache step,
  pre-built olean tree). Machine at start: `nproc` 4, 16 GB RAM (about 15 GB available).

## Ladder status (checkpoint 1)

| Step | Lemma | Status |
|---|---|---|
| 1 | `statClose_sampleColorPair` | filled |
| 4 | `exists_colSimRed_fixCoins`, `colSimRed_fixed_eq` | filled |
| 5, 2, 3, 6, 7 | | in progress |

Evidence: `evidence/check-cp1-Simulator.log`, `evidence/lint-before.log`.
