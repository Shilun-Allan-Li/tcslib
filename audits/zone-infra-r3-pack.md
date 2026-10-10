# External audit pack — zone/virtual-input layer (§13), tranche A-S2, round 3

Round 2 (`audits/zone-infra-r2-pack.md`, findings verbatim in
`audits/zone-infra-r2-findings.md`) **accepted the round-1 operational
repair and closed the Z4 route major**, and returned **one blocker on the
repair's own cascade contracts** (A-S2-R2-1: the top-left receiving room
omitted) and one inventory minor. This round audits those repairs.
Audited at the commit carrying them (branch
`complexity/arora-barak-ch3-4`; the repaired `Build/Zone.lean` is attached
in full, 647 lines). The gate closes on zero blockers and zero majors.

## Disposition table (verify each)

| Round-2 finding | Disposition |
|---|---|
| A-S2-R2-1 (blocker: both cascade contracts false without top-left room) | **Repaired exactly as you proposed.** `zoneCascadeRight_lengths` gains the **necessary** hypothesis `(z.left ⟨j, hj⟩).length + 2^j ≤ zoneCapacity j` (your necessity argument — the conclusion plus `left_le` — is quoted in its docstring, with the classical-invariant implication showing no textbook pre-state is excluded); `zoneSide_cascadeRight` gains your weaker sufficient form `+ 2^(j-1)` (at `j = 0`, `+1` by natural subtraction), with the one-pass boundary instance recorded in the docstring as the reason the two hypotheses differ. Both sketches adopt your two-pass induction and your word-equality argument verbatim as the binding routes (the word proof explicitly does **not** use half-full restoration). The requested regressions are added: `zoneCascadeRight_zero` (the `j = 0` instance) and `zoneCascadeRight_blocked` (the full top receiver: every outward-left guard fails, the move is blocked, both represented words unchanged). Re-run your `ℓ = 1, j = 0` counterexample (now excluded by `hroom`), your `(2,4)/(0,2)` and `(2,3)/(0,2)` traces (the first excluded by both hypotheses; the second satisfying the word form and failing the lengths form, as intended), and your repaired-schedule induction against the amended statements. |
| A-S2-R2-2 (minor: inventory) | **Acknowledged; your inventory is adopted as canonical**: `Zone.lean` 20 definitions/structures (now 20 + 0 — the repair adds 2 sorried theorems and 2 regression theorems, no definitions), 18 + 4 = **22 sorried declarations**, 22 + 2... recount: the repair adds four sorried theorems and no definitions, so the attached file carries **24 literal `sorry` terms over 22 sorried declarations, 20 definitions, 2 skeleton proofs** — verify this round-3 count yourself and treat your own recount as authoritative for the fill brief. Tranche totals adjust accordingly (the `Codes2Tape` and Z4 rows are unchanged). |
| A-S2-R2-3 — A-S2-R2-9 (accepted dispositions and no-findings rows) | Carried unchanged; nothing in this delta touches the raw ops, wrappers, `zoneMove`, the cost lemma, the Z4 sketches, `Codes2Tape.lean`, or the design §13c boundary. Verify the delta is confined to the two cascade contracts' hypotheses/docstrings, the two new regressions, and the module header's status/export lines. |
| A-S2-R2-10 (evidence boundary) | Carried explicitly: elaboration (exit 0, 0 errors), lint (0 FAIL), and historical byte identity remain maintainer attestations; this packet again ships current source, the prior packs, and both prior findings. |

## Brief for the auditor

1. Verify the disposition table against the attached source: blind-restate
   the two amended contracts and the two regressions; check the amended
   hypotheses are exactly your proposed forms; re-run your round-2
   counterexamples and your repaired-schedule induction.
2. Hunt for any **new** defect introduced by the repair: in particular,
   whether `zoneCascadeRight_blocked`'s hypotheses really force every
   outward-left guard to fail (lower-left fullness leaves no room at any
   receiving level), and whether `zoneCascadeRight_zero`'s hypotheses
   match the `j = 0` specializations of the main contracts.
3. Report in the standard table; findings verbatim into
   `audits/zone-infra-r3-findings.md`; the gate closes on zero blockers
   and majors, after which the A-S2 fill brief is drafted (your round-1/2
   arguments, numbers, and regressions embedded as the binding routes).
