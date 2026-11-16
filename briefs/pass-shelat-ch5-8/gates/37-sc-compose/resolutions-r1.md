# Gate 37 · resolutions, round 1 · HOLD → round 2

Codex's verdict is **HOLD**: 0 blockers, 2 majors, 1 minor.
- **Findings:** `findings/gate37-sc-compose-findings.md`, SHA-256 `21203fb8ce90ef6f86346b0042fabbc10ef7da2a5f8ac31d484f481543877ae2`. The evidence ZIP was not supplied.
- **Audited head:** `a6eaebd78c48e7fdfd06263edb84b70bc00ec593`, records `c4455759`, exchange `5fab5874`.

The proof audit found no mathematical defect in the three targets. Codex checked:
- efficiency, by the raw-function identities;
- security, through all five steps, with ε = ε_A + ε_B;
- the edge cases: zero calls and zero rounds;
- the freeze (185/0/0), Rule 10, the axioms, the builds and the scope.

| # | Severity | Disposition |
|---|---|---|
| G37-01 | major | **To be fixed by LE-gate37** (Seyoon's ruling, 2026-11-16: re-point via import). `ComposeMachines.encodeMsgs_append` (`ComposeSecurity/Machines.lean:143`) is re-derived from the public `CommitmentLemmas.encodeMsgs_append` (`ZeroKnowledge/CommitmentLemmas.lean:233`). Only the proof changes; the header is kept. `ZeroKnowledge.CommitmentLemmas` is imported: acyclic, +47 modules. |
| G37-02 | major | **To be fixed by LE-gate37**, the same way. `ComposeBound.length_encodeMsgs_le` (`ComposeSecurity/Bounds.lean:53`) is re-derived from the public `CommitmentLemmas.length_encodeMsgs_le` (`:241`). Only the proof changes; the header is kept. |
| G37-03 | minor | **To be fixed by LE-gate37, docstrings only.** The formulas of eleven readers were truncated with `…`: `asmView_eq`, `asmW_eq`, `runW_eq`, `ansW_eq`, `composePW_eq`, `composeVW_eq`, `goodRuns_iff`, `sampleA_eq`, `sampleB_eq`, `phiV_eq` and `hybW_eq`. Each gets its complete formula. |

**Record correction:** LE-doc has 20 truncated insertions (16 distinct prefixes), not the 15 the pack stated.

**Next:** LE-gate37 on `land/pass-shelat-sc-compose`, with the overlap record corrected. Then a rebuild and re-seal on the tip, and Gate 37 round 2.
