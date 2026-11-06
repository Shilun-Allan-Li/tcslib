# Gate 03b (one-wayness and collections): round 3 resolutions — gate closed

- **Round 3:** findings `findings/gate03b-r3-findings.md`, verbatim, SHA-256 `8925ca3541b0c2e536f3aa24865e6a9acaf044b38aaadb6dc268e35550bb0363`; pin
  `4769fe88d6894a62c87a19bc524088c5a2c99e0b` (Lean = #204's head `08fa1185`); bundle `fa465a29…`.
  **0 blockers, 0 majors, 1 minor, 2 notes.** R2-1, R2-2 and R2-3 are fixed. The auditor proved the
  corrected `ofString` bound (additive term `2^{-n/2}` at positive even lengths, 0 otherwise),
  and the round 2 attack now succeeds only with probability `2^{-k}`.
- **The gate closes** (0 blockers, 0 majors).

| Finding | Severity | Resolution |
|---|---|---|
| R3-1 | minor (inherited, outside the delta) | **Scheduled** (the gate 03 repair batch, item A): `WorstCaseOneWayLit.toParam`'s docstring (`OneWay.lean` ~:283–285) still calls injective output length "the case of every family of the text"; it becomes "injective `outLen`, equivalently non-constant output length for these polynomial lengths". No statement changes. |
| R3-2 | note | No change: the repaired example respects the zero padding. |
| R3-3 | note | No change: exactly the two specified docstrings changed. |
