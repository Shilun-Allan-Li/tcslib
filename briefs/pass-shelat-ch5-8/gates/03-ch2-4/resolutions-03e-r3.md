# Gate 03e: round 3 resolutions — gate closed

- **Round 3:** findings `findings/gate03e-r3-findings.md`, verbatim, SHA-256 `5346a47806dfc65158f69bb426aa56879086431df5aa720e6514096cc6ad1977`; pin
  `1ea782b11617e15a51c3e2f6bd15dd0e3befbd95` (the merge of #206; repair head `73751f57`); bundle `c59bf71c…`.
  **CLOSE: 0 blockers, 0 majors, 1 minor.** Round 2: #1, #2, #4–#7, M1, M3, M4 fixed; #3, M5
  recorded (the edited record files were not bundled); M2 scheduled (clean-up part 2).

| Finding | Severity | Resolution |
|---|---|---|
| 1 | minor | **Confirmed and scheduled** (clean-up part 2, item K). `ZeroKnowledge/Defs.lean:33–35`, the D8 deviation paragraph, still says "the theorems become statistical", which contradicts the GI/3COL distinction of the next paragraph and of DESIGN §5 item 11. The parenthesis is replaced by the auditor's wording: expected polynomial time is not formalized; GI uses a truncated simulator and obtains statistical ZK, while 3COL remains computational ZK with statistical sampling and failure terms. A docstring change only. |
| R2 #3, M5 | (round 2) | **Recorded.** The edits to `run3-audit-summary.md` (line 17), `SPINE-DESIGN.md` §S1 and `inventory-ch5-8.md` (Thm-175.1) are on the records branch at `1ea782b1`; they can be bundled into any later pack that cites them. |
| R2 M2 | (round 2) | **Scheduled:** clean-up part 2 (equation lemmas, `firstHit_eq`, the tactic-level unfolds). |
