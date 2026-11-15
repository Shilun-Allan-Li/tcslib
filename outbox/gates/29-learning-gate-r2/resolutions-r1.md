# Gate 29 · resolutions, round 1 · HOLD → round 2

Codex's verdict is **HOLD**: 0 blockers, 2 majors, 0 minors, 0 notes.
- **Findings:** `findings/gate29-learning-findings.md`.
- **Audited head:** `8befc58966fd39f974a54250849736df194584b9`.
- Codex found the proof correct, part (c) sorry-free and the frozen statements intact. The seals and controls pass.
  Both majors are re-proofs that the review missed and nobody disclosed.

| # | Severity | Disposition |
|---|---|---|
| G29-01 | major | **Fixed by LE-gate29a, proof only** (`94b31964ee94b97bf3ed3b4b4338cacae8183194`, tree `b283709e`). The four-line calculation in `hj` is now `simp only [uprob_eq_point, OneWay.uexp_const]`, no new import; the sketch names the lemma. `decls2` empty, headers 63/63 identical. Evidence `landing-r1/gate29-le-a-evidence.zip`, SHA-256 `b1ce1c5057d7b836d0546562a7f7dab503e4b5237fb28939bcf61ffc96fcffb2`. Pushed to #313. |
| G29-02 | major | **Ruling (Seyoon, 2026-11-15): promote it now.** The new `firstBit_of_pos` re-proves the zero-index case of the public `LamportFill.headD_drop_ofFn`. A small PR promotes `headD_drop_ofFn` to a shared list layer that is upstream of both consumers, and re-derives Lamport's copy proof-only. After that PR merges, #313 re-points `firstBit_of_pos` (LE-gate29b), and Gate 29 round 2 follows. |
