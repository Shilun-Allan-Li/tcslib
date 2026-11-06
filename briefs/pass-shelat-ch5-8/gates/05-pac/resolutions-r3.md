# Gate 05 (PAC layer, #194): round 3 resolutions — **the gate is closed**

- **Round 3:** findings `findings/gate05-pac-r3-findings.md` on #194 at `f0385dac`: **0 blockers, 0
  majors, 2 minors (R3-1, R3-2)**. R2-1, R2-2, R2-3, F5, F6, F11 and F14 confirmed **fixed**.
- **The gate closes** (0 blockers, 0 majors). The two minors are fixed in a final docstring-only
  commit, #194 → `27d0b96d436a4b8d489baf6dca0bfcaab7f7e8dd`; the maintainer re-checked the three changed modules (no
  diagnostics) and lint (0).

| Item | Severity | Resolution |
|---|---|---|
| R3-1 | minor | **Fixed.** `WeakLearnsUnder` and `WeakLearns` say "for every concept `C i`"; the [KV94, §4.1] comparison is stated on a slice with fixed instance dimension and target size (one `m`, edge and confidence for every concept of the slice), noting that common values must be obtained across target sizes. |
| R3-2 | minor | **Fixed.** `PAC.lean`'s contents line, `Prediction.lean`'s "Use in layer 2" paragraph and `not_weakLearnsUnder_of_predictAdv_le`'s docstring (and the S3d note) say amplification is needed only when the learner is not already certified at the required confidence. |
