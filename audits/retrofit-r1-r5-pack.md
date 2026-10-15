# External audit pack — chapter-1/2 retrofit, epoch R1 boundary, round 5

Round 4 (`audits/retrofit-r1-r4-pack.md`, findings verbatim in
`audits/retrofit-r1-r4-findings.md`) **verified the entire round-3
reconciliation** (the 19+1 counter block, the Composition privates, the
in-file pairs, the 289/283 arithmetic, all denominators, the A2 report's
45-entry reconciliation, the sampled remainder) and closed R3-2 and the
Wrappers estimate — holding the gate on **R4-1**: two strengthened
**public** correspondences the census missed (`computesFunInTime_id`/
`_const` reproduce their Composition time proofs inside Catalog's
`_spaceUsed` rows), with the demanded repair being the completed census
plus a systematic screen of the remaining public targets. This round
audits that screen and the final census. The gate closes on zero blockers
and majors.

## Disposition table (verify each)

| Round-4 finding | Disposition |
|---|---|
| R4-1 (major: the two public correspondences; the demanded screen) | **Repaired with the systematic screen you demanded.** Method (stated in the ledger for reproduction): every public `computesFunInTime_*` of `Composition.lean` and `Build/Primitives.lean` with a Catalog `_spaceUsed` counterpart, screened for reproduction of its proof inside the counterpart's time conjunct — normalized comment/whitespace-stripped containment after `f2_` renaming, segments ≥ 60 characters. **Results: exactly your two Composition hits; all 16 screened Primitives rows distinct** (their space-row proofs are the separate trajectory arguments the F2A per-target routes describe — your own round-4 sampling of the remainder corroborates). The ledger now counts both public pairs on both sides: **Catalog 291/423 = 68.8% expanded, 283 = 66.9% strict** (the two new counterparts join the strengthened exclusions); **Composition 5/19 = 26.3%** (strict 3). A coverage qualification is recorded: the screen detects substantial contiguous reproduction, not sub-threshold partial adaptation. **Reproduce the screen** from the attached four sources (the method is mechanical) and verify the no-hit verdicts on a sample of the 16. |
| R4-2 (minor: the F2A decomposition and the stale label) | **Fixed**: the ledger states `306 = 150 + 94 + 10 + 3 + 20 + 2 + 27` with the two in-file originals called out as previously double-described; the acknowledgment table's family label updated from the stale 264 to the expanded 291. |
| R4-3 (minor: span figures) | **Fixed with your measured values throughout**: Loop partition 2,200 (the 22-line `f2_loopHost_contracts` docstring/closure-note inclusion), listed-union 6,202, expanded 291-member **6,267**, counter 345, TimeConstructible 355, Composition 51 + 46 = 97; estimates eliminated. |
| R4-4 — R4-10 (verified reconciliations and carried closures) | Carried as recorded; this round's delta is the ledger, this pack, and the plan's decision log — no Lean source changed. D-R2/D-R3/RB4 stand; nothing requests re-approval. |

## Brief for the auditor

1. Reproduce the public-proof screen from the attached `Catalog.lean`,
   `Composition.lean`, `Build/Primitives.lean`, and
   `ClassP/TimeConstructible.lean`; verify the two hits and sample the
   sixteen distinct verdicts.
2. Verify the final census arithmetic (291/283, 5/19, 20/21 with strict
   19, the measured spans) and that the acknowledgment table's labels now
   match it.
3. Confirm no remaining recorded correspondence, agent-declared copy, or
   screen hit is outside the ledger; if one exists, name it.
4. Report in the standard table; findings verbatim into
   `audits/retrofit-r1-r5-findings.md`; the gate closes on zero blockers
   and majors, retiring epoch R1 and arming 12.2c and RB4 (RB4's window —
   the A-S1 fill-gate close — is already open; its brief is issued).

## Repository-side attestations

As rounds 1-4; documentation-only delta this round.
