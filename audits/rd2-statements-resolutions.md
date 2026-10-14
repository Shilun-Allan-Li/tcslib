# RD-2 statement gate: resolutions

**Gate:** `audits/rd2-statements-pack.md`; bundle `audits/rd2-statements-bundle.md`, SHA-256
`b873469afca84f2683f18f9ec2a2d1f73972527dfc3b0fa6aeb25d11e8a3c15f`, 63 sections.
**Findings:** `audits/rd2-statements-findings.md`, verbatim.
**Verdict: PASS, CLOSED in round 1 (2026-10-14): 0 blockers, 0 majors, 2 minors, 12 notes.** No
counterexample to a proposed theorem. No statement changes.

| # | Severity | Finding (short) | Resolution |
|---|---|---|---|
| 1 | minor | `polyTimeComputable_flatMap_range`'s sketch bounds initialized iterates by `x.length + count x + O(1)`; the aligned pairing doubles the first component | Accepted. At landing, the sketch states the initialized-orbit bound `2·x.length + count x + 2`, and distinguishes it from `polyTimeComputable_emitIter`'s all-start-word orbit bound. That bound covers an oversized second component and malformed pairs, by saturation and the total pair projections. This is docstring-only. |
| 2 | minor | The duplication ledger missed `fragment_append` (a twin of `CookLevin.clFragment_append`, with its one-line `simp` proof) and overstated "one-line, identical bodies" | Accepted. `fragment_append` joins the Cook–Levin re-basing family. MERGE means correspondence of definitions and interfaces after renaming, not identical proofs: the public `cost_flatMap_le` is admitted, while its private predecessor is proved. `UnaryPT.add` overlaps in statement and is not a proof twin. The copied-proof count for the listed families is **seven nonblank tactic lines** (Gate 2, Emit 2, codec 3): small accounting debt inside the disclosed promotions and re-basing, not a new family. |

**Note 14:** Finding A means that no uniformity contract or algorithm is supplied for the literal
choices. It is not a proved noncomputability lower bound. The records use that wording.

**Next:** the landing PR, carrying the proposed files unchanged apart from row 1's sketch fix.
Then the semantic re-fill RD-2a (the migration list) and the uniformity fill RD-2b.
