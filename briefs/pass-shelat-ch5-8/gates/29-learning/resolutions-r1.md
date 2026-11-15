# Gate 29 · resolutions, round 1 · HOLD → round 2

Codex's verdict is **HOLD**: 0 blockers, 2 majors, 0 minors, 0 notes.
- **Findings:** `findings/gate29-learning-findings.md`.
- **Audited head:** `8befc58966fd39f974a54250849736df194584b9`.
- Codex found the proof correct, part (c) sorry-free and the frozen statements intact. The seals and controls pass.
  Both majors are re-proofs that the review missed and nobody disclosed.

| # | Severity | Disposition |
|---|---|---|
| G29-01 | major | **Being fixed by LE-gate29a, proof only.** The local `hj` in `abs_gameProb_random_sub_half_le` re-proves `OneWay.uexp_const`. It will use that lemma instead, with no new import. |
| G29-02 | major | **Ruling (Seyoon, 2026-11-15): promote it now.** The new `firstBit_of_pos` re-proves the zero-index case of the public `LamportFill.headD_drop_ofFn`. A small PR promotes `headD_drop_ofFn` to a shared list layer that is upstream of both consumers, and re-derives Lamport's copy proof-only. After that PR merges, #313 re-points `firstBit_of_pos` (LE-gate29b), and Gate 29 round 2 follows. |
