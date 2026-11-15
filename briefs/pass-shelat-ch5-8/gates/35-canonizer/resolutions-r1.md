# Gate 35 · resolutions, round 1 · CLOSED

Codex's verdict is **CLEAR**, with no findings (0/0/0/0).
- **Findings:** `findings/gate35-canonizer-findings.md`, SHA-256 `932a349b668ef987280c39867b30a8d13033719b1375b57c86f1d681e47ee61f`. Codex's evidence ZIP was not supplied; the Markdown is the record.
- **Audited head:** `6421ac1631ef08feed297c810f0839b178d2a2bb`, records `034da63a`, exchange `8b5e96ad`.

Codex confirmed the following:
- The proof establishes the frozen existential, and the bound `d(k+1)^d ≤ d·2^{dk}` holds, including at `k = 0` and `d = 0`.
- Both readers are exactly the pre-approved ones. Deleting their added lines recovers each base file byte for byte.
- The axiom closure (8,151 constants) contains neither `appendBitTM_computes` nor `sorryAx`. Codex checked this against the traversal in Lean's `FoldConsts`.
- **C-F01** is accepted as an LE-width-class disposition: it only changes whitespace.
- The Rule-10 tables match those of the base. The full-file `-DmaxErrors=0` CodeSimulator seals give 177 → 177 errors, with the same 58 declarations.
- No undisclosed duplication was found.

**Gate 35 is CLOSED.** One merge condition remains: an integration rebuild against the tip, which now contains #316 and #317. If #318 merges first, the rebuild must be against #318 as well.
