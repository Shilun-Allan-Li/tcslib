# External audit pack — chapter-1/2 retrofit, epoch R1 boundary, round 6

Round 5 (`audits/retrofit-r1-r5-pack.md`, findings verbatim in
`audits/retrofit-r1-r5-findings.md`) verified the two recorded Composition
pairs, the listed 291/283 census, and its physical spans. It held the gate on
two majors and one minor:

- **R5-1:** the `f2_strip_linear` adaptation of the public
  `computesFunInTime_stripLast` was uncounted.
- **R5-2:** the published screen did not reproduce. The stated ≥ 60-character
  method yields six Primitives fragment hits beyond the two recorded pairs.
- **R5-3:** the population has 15 Primitives rows, not 16.

This round audits the repair: a published, executable screen with an explicit
classification rule, and the census it produces. The gate closes on zero
blockers and majors.

## Disposition table (verify each)

| Round-5 finding | Disposition |
|---|---|
| R5-1 (major: the `f2_strip_linear` adaptation) | **Repaired, and the screen behind it widened.** `f2_strip_linear` is counted on both sides. It reproduces 86.0% of `computesFunInTime_stripLast`'s proof; the shared-text measure is defined in the R5-2 row. The **residual pass** you asked for screens all 27 recorded nonmembers against every public proof of Composition, Primitives and TimeConstructible, taking each one's best match by shared length. It finds a **second adaptation**: `f2_counter_heads` reproduces 64.1% of `timeConstructible_id`. This is your 215-character partial-reuse candidate, which crosses the member bar once measured by tiling, so it is counted too. Six residual fragments are recorded and not counted, including `f2_cond_time` against `bufferedCompTM_computesInTime`, which your report did not list. |
| R5-2 (major: the screen does not reproduce) | **Repaired with a published, executable screen and an explicit rule.** Files: `audits/evidence/retrofit/r1-public-proof-screen.py`, with its output `r1-public-proof-screen.out` (both attached). *Erratum:* the round-4 run tested whether each source proof was contained whole in its counterpart, while the round-4 text described "segments ≥ 60". The screen reports two measures. The **literal LCS** reproduces your hit set exactly (776 / 273 / 62 / 75 / 75 / 75 / 91 / 121). The **shared length**, from greedy tiling with blocks of at least 25 characters, is measured as a fraction of the **source** proof; this is R4-1's own standard, that the source proof is reproduced inside the target. **Rule:** a pair is a member when at least half the source proof reappears, with an absolute floor of 60 characters so that a short citation of a public lemma counts as reuse; any other shared tiling of at least 60 characters is a recorded fragment. Every candidate gets a named disposition; none is reported as "no hit". The rule is deliberately inclusive. It makes **five more Primitives pairs members**: `prepend`, `pairEncodeFixed`, `pairFst`, `pairSnd` and `pairConcat`, each reproducing 89–100% of its source. `pairEncodeFixed` has a 53-character LCS, below your literal threshold, but its whole 91-character source proof reappears. Three direct pairs are recorded fragments (`polyUnary`, `pairLenCheck`, `stripLast`). |
| R5-3 (minor: population) | **Fixed.** 17 eligible pairs: 2 from Composition and **15** from Primitives. The five unmatched source theorems are named in the ledger. |
| R5-4 — R5-9 (verified reconciliations and carried closures) | Carried as recorded. This round's delta is documentation only: the ledger, the screen evidence, this pack, and the plan's decision log. No Lean source in the screened files changed. The census grows inside the already-acknowledged D-R2 family; nothing requests re-approval. |

## The resulting census (verify)

| File | Members | Fraction | Lines |
|---|---:|---:|---:|
| `Build/Catalog.lean` | **298** = 291 + 7: the two adaptations plus the five new strengthened public counterparts | **70.4%** (strict **283**, 66.9%, unchanged) | **6,491** = 6,267 + 224 (64 + 45 + 22 + 16 + 26 + 24 + 27) |
| `Build/Primitives.lean` | **156** = 150 + 6 public originals | **57.4%** | **3,407** = 3,162 + 73 + 81 + 91 |
| `ClassP/TimeConstructible.lean` | 20 (unchanged; `timeConstructible_id` was already an original-side member) | 95.2% | 355 |
| `TuringMachine/Composition.lean` | 5 (unchanged) | 26.3% | 97 |

F2A: `306 = 150 + 94 + 10 + 3 + 20 + 2 + 2 adaptations + 25 nonmembers`. Strict:
`298 − 14 strengthened counterparts or adaptations − 1 counter near-copy = 283`.
The new spans were measured by the screen's span routine, which reproduces your
four reference measurements exactly: `stripLast` 81, `f2_strip_linear` 64, and
the `id`/`const` targets 44/21.

## Brief for the auditor

1. Run or reconstruct the attached screen against the attached sources. Verify
   both passes, the rule, and the seven new member verdicts. Sample the fragment
   and citation verdicts.
2. Verify the census arithmetic and spans above, and that the acknowledgment
   table's family label now reads 298.
3. Judge the rule. If you consider any recorded fragment a member, or the reverse,
   name it with evidence. The rule is meant to be conservative, counting more
   rather than less.
4. Confirm that no recorded correspondence, agent-declared copy, or screen
   candidate is outside the ledger; if one is, name it.
5. Report in the standard table, with findings verbatim into
   `audits/retrofit-r1-r6-findings.md`. The gate closes on zero blockers and
   majors, retiring epoch R1 and arming 12.2c. RB4's window is already open.

## Repository-side attestations

As in rounds 1–5; this round's delta is documentation only. Since round 5, the
branch has gained the ch7 merge (PR #11) and the zone-f1 A/C fills, none of which
touches the screened files: Catalog, Primitives, Composition and TimeConstructible
are byte-identical to the round-5 bundle's attachments.
