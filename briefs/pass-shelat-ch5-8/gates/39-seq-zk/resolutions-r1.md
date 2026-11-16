# Gate 39 · resolutions, round 1 · HOLD → round 2

Codex's verdict is **HOLD**: 0 blockers, 1 major, 0 minors, 0 notes.
- **Findings:** `findings/gate39-seq-zk-findings.md`, SHA-256 `98be3c2237cb36981087f4e941d0e7e429c9db28226db6fef272805cdfe8f618`.
- **Audited head:** `bd19c433a4cf3d4027ffc891d7d3c06e927e9dfa`, records `d5a3e2d0`, exchange `da8f8f66`.

Codex found no mathematical defect in the five target proofs. It confirmed:
- `SQ` is uniform.
- The ZK and statistical-ZK error bounds are `Q·|ε|` and exactly `Q·δ`.
- The adaptive soundness bound is `s^Q`.
- The boundary cases hold.
- The freeze holds at 196/0/0.
- S-01 is `Iff.rfl`.
- LE-doc changes docstrings only.
- Rule 10 adds 0 new failing declarations.
- The axioms are standard.
- The ownership and final-sweep records are consistent.

The 11 truncated formulas are acceptable: their prose states the omitted property.

| # | Severity | Disposition |
|---|---|---|
| G39-01 | major | **Fix by LE-gate39** (proof only; the same practice as G36-01). The local `hsource` in `PaddedProverSpec.realPrefix_bounds` (`SequentialZK/RealPrefixBounds.lean:83`) re-proves the PR's own public `PaddedProverSpec.next_length_le` (`ProofTransfers.lean:38`). It becomes `d.next_length_le y B hbound tape hist`, with an import of `SequentialZK.ProofTransfers` (acyclic). Headers are kept and the overlap record is corrected. #327 and the combined tree are rebuilt, then Gate 39 round 2. |
