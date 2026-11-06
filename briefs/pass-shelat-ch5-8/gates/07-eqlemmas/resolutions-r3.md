# Gate 07 (equation-lemma PR #210): round 3 — CLOSED

- **Round 3:** findings `findings/gate07-eqlemmas-r3-findings.md`, verbatim (delivered by upload), SHA-256
  `8dde479b68852f6e0b56023d230f746b3b335b66957b80d5d52f55534779560b`; head `eb99dd7bb2d8a270b2ce17a3cf3e1487a65ad0ee`.
  **Verdict PASS: 0 blockers, 0 majors, 0 minors.** R2-01, R2-02, R2-03 fixed; F02 fixed (F01, F03 fixed in
  round 2). The auditor reproduced the declaration tables byte for byte, the `sorry` counts, and the replay's
  105-module closure, and confirmed the probe/control attribution.
- **Gate 07 closes at `eb99dd7bb2d8a270b2ce17a3cf3e1487a65ad0ee`.** Recorded deferred work (not certified by the gate):
  the 764 (b) rule-10 rows in 468 untouched declarations (`evidence-r2/r6c/cleanup-b*.tsv`) for clean-up part 2;
  #195's own repair, audited by gate 04.
- Note from round 3: `pack-r2.md` keeps its superseded `sorry`-baseline sentence; the correction is in
  `resolutions-r2.md` and `pack-r3.md`.
