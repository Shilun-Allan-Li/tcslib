# Gate 39 · resolutions, round 1 · HOLD → round 2 CLEAR → CLOSED

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
| G39-01 | major | **Fixed by LE-gate39** `a94ba750b2f21ea5f2c3e58bc7959ad5ac9de871` on `bd19c433` (proof only; the same practice as G36-01). The local `hsource` in `PaddedProverSpec.realPrefix_bounds` (`SequentialZK/RealPrefixBounds.lean:83`, now `:85`) re-proved the PR's own public `PaddedProverSpec.next_length_le` (`ProofTransfers.lean:38`). It is now `d.next_length_le y B hbound tape hist`, with an import of `SequentialZK.ProofTransfers` (acyclic; it adds only that module to the closure). The header is unchanged, and the sketch gains one sentence naming the public theorem. Evidence: `landing-r1/gate39-le-evidence.zip` (SHA-256 `35e990e7cafba0222ee96e8618ccc52d70479b43d6e0fe4f399b19fa7643c85b`, 934 manifest files) and its `PROVENANCE.txt`. It shows decls2 against `bd19c433` empty, #327 alone on the tip 679/679 rc 0 (admissions 202 → 197), the final combined tree 26/26 rc 0 (admissions 194), the seals of `RealPrefixBounds` passing, and standard axioms. The overlap record: the duplicate is removed, so no ledger row (as for G36-01); this table and the decision log record it. **Round 2 staged:** `pack-r2.md` and the round-2 files beside it; the Codex prompt is `dispatch-r2.md`. |

**Next:** Gate 39 round 2 (Codex) at `a94ba750`.

## Round 2 (2026-11-16): CLEAR, gate CLOSED

Codex round 2 (`findings/gate39-seq-zk-r2-findings.md`) at head `a94ba750b2f21ea5f2c3e58bc7959ad5ac9de871`: **CLEAR**, 0 blockers, 0 majors,
0 minors, 0 notes. G39-01 is **closed**: `hsource` is the public `next_length_le`, the added import is acyclic
(closure 144 → 145, only `ProofTransfers`), headers and prose unchanged, decls2 against round 1 empty. The
rebuild, seal, control and axiom evidence verified independently (679/679; combined 26/26; admissions
202 → 197 and 194; snapshot restored). No new undisclosed duplicate (175 new theorems scanned against 20,640).
The round-1 confirmations hold. **Gate 39 is CLOSED.**
