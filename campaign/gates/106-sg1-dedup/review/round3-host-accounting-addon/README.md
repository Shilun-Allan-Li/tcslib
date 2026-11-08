# Post-ruling unary-clock host accounting

**Not yet clear to merge: #215.** This is an accounting addendum, not gate clearance. The pre-ruling `round3-accounting-review/` remains frozen and historical.

Root conveyed Seyoon's explicit acceptance of the existing generic unary-clock host kind across TCSlib: arbitrary positive clean-call unary repetition, with matching frame/run/output/budget facts and actual-orbit polynomial wrappers. Cleanup belongs to the maintainer in the next12.2c window after active MIG1 and before further SAT/Hardness fills, through shared-host design, gate and repoints. The ruling grants no new API, import, or permission for future private hosts. Root records the canonical user approval and ledger entry.

The proposed current Hardness members are exactly:

| Member | Kind | Source line |
|---|---|---:|
| clRepeatTM | def | 5649 |
| clRepeatCfg | def | 5668 |
| clRepeat_frame | lemma | 5677 |
| clRepeat_call | lemma | 5697 |
| clRepeat_round | lemma | 5746 |
| clRepeat_complete | lemma | 5780 |
| clRepeatWords | def | 5814 |
| clRepeat_initial | lemma | 5818 |
| clRepeatOutputTM | def | 5828 |
| clRepeatOutput_compute | lemma | 5838 |
| clRepeat_budget | lemma | 5954 |
| clRepeatArgument_native | lemma | 5990 |
| clA5Iter_native | lemma | 6763 |
| clA5Iter_shrinking | lemma | 6798 |

All14 are distinct authored private declarations: four definitions and ten lemmas. They are disjoint from the prior32-member named set and the three added clFill members. Thus **35 +14 =49**, with the unchanged source denominator544, is defensible as the current **named affected-declaration lower bound49/544 (9.01%)**. It is not49 confirmed duplicates, not49 new acknowledgments, and not an exhaustive census. Prior watch/acknowledgment distinctions remain separate.

`disjoint-accounting.json` retains both complete sets, their empty intersection, all14 actual headers/locations, source hash `a6edf9fe11e89d71a028143d1cedf9be896124bbcbc5a86d779e6c6278b5c597`, the complete49-member union and the pre-ruling manifest pin. No source, Lean, screen or Git operation was performed for this accounting check. This ruling does not silently dispose of the separate on-image class-wrapper assessment.
