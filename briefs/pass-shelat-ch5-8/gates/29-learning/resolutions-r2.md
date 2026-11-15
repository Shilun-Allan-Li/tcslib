# Gate 29 · resolutions, round 2 · CLOSED

Codex's verdict is **CLEAR**: both round-1 majors are closed, and there is no new finding (0/0/0/0).
- **Findings:** `findings-r2/gate29-learning-r2-findings.md`, SHA-256 `8d6ed3e4e6c59fa797fceeb072e03fef410581422c596f0d81341cdb0e0b39ad`.
- **Audited head:** `2b6c29816de4cb1cd0e6b74fa3ae848c9f0f1be9`, records `fb8737f8`, exchange `3de4f1a6`.

| # | Round 1 | Round 2 |
|---|---|---|
| G29-01 | major | **Closed.** LE-gate29a: `hj` uses `OneWay.uexp_const`, proof only. |
| G29-02 | major | **Closed.** LE-gate29b: `firstBit_of_pos` follows from the merged `TCSlib.Cryptography.headD_drop_ofFn`, proof only. |

Codex also confirmed the following:
- Since round 1, only the two repairs change. The 61 headers, the definitions and the imports are preserved, and part (c) is unchanged.
- The rebase's range-diff is identical. The closure grows from 138 to 141 modules because of #314–#317.
- No new duplication appeared.
- The 268-module integration build, the seals, the axioms and the admission count (39 → 38) are verified.
- The live PR description is current.

**Gate 29 is CLOSED.** One merge condition remains: an integration build against #323. They share 7 modules, so whichever of
the two merges second needs it. #318, #319 and #324 share only root `TCSlib` or `Randomness`. The combined build of
the tip, #313, #323 and #324 is running.
