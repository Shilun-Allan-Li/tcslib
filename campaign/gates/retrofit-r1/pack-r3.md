# External audit pack — chapter-1/2 retrofit, epoch R1 boundary, round 3

Round 2 (`audits/retrofit-r1-r2-pack.md`, findings verbatim in
`audits/retrofit-r1-r2-findings.md`) **closed R1-1, R1-3, and R1-4**
(full bidirectional reconstruction with recomputed blobs; the E1
statements proven identical up to renaming; the errata confirmed) and
held the gate on the ledger: **R2-1** (inconsistent arithmetic, no single
inclusion rule, missing sources) and **R2-2** (debt: the relocation
family's "reimplementation" classification refuted — byte-identical
across the three files — and the H3 copies omitted, with no named cleanup
owner/window). This round audits the ledger rebuild and the human
acknowledgment. The gate closes on zero blockers and majors; debt majors
close only by human acknowledgment — **which has now been given**.

## Disposition table (verify each)

| Round-2 finding | Disposition |
|---|---|
| R2-1 (major: ledger arithmetic and convention) | **Rebuilt** (`audits/duplication-ledger.md`, attached): one primary inclusion rule (expanded correspondence membership, strengthened counterparts included symmetrically; strict normalized-twin counts stated secondarily where they differ), every family enumerated once per file, your independently computed figures adopted verbatim — Loop **104/212 = 49.1%** (87 + 4 relocation originals + 13 H3 copies), Primitives **150/272 = 55.1%** (146 + 4), Hardness **4/549**, Catalog **264/423 = 62.4%** (150 + 95 + 17 + 2; strict 259 = 61.2%), Wrappers **17/29 = 58.6%**; your span-rule line counts (2,009 / 3,162 / 73-per-file) adopted with the rule stated; deleted-original/dead-twin labels downgraded to 12.2c dispositions requiring the Catalog reference graph. The previously missing sources are attached: **the complete pinned `Build/Catalog.lean` and `Build/Wrappers.lean`**, plus the A2/F2A agent reports whose declared-copy inventories the correspondences cite. Recompute the totals and fractions; flag any member the rule still misses. |
| R2-2 (major, debt: the relocation family and H3 copies) | **Accounted and acknowledged.** The ledger now counts the three-file relocation family once per file (12 members in all) under its correct classification — verbatim copies, pre-policy legacy, disclosed at their batches but mischaracterized by the round-1 ledger — and the 13 H3 copies in Loop's row (originals not double-counted; the `_init` near-copy noted, uncounted). **The human acknowledgment is on record** (the user, 2026-10-09, via the plan's decision log and the ledger's acknowledgment table): cleanup owner — **retrofit batch RB4** over all three files, collapsing the H3 copies via the proved §13 Z5 agreement transfer and replacing the relocation family via the proved Z1-rider selected-tape exports plus Z5; window — **after the A-S1 fill gate closes** (Z5 and the rider are proved as of vhost-f1). Verify the acknowledgment names family, owner, and window as the governance requires, and that D-R2/D-R3 are carried without renewed approval, per your own round-2 guidance. |
| R2-3 (minor: delta wording) | **Fixed**: eleven dead originals plus one live original eliminated by replacement; the epoch-wide 76 + 7 distinction retained. |
| R2-4 — R2-11 (closed and no-findings rows) | Carried as recorded; nothing in this round's delta touches sources — the only changed artifacts are the ledger, the plan's decision log, and this pack. |

## Brief for the auditor

1. Verify the rebuilt ledger against the attached sources and
   correspondences: recompute at least the Catalog 264 partition (now
   fully attachable: count the `f2_*`/`a2_*`/`catalog_redirect*` members
   in the attached `Catalog.lean` against the attached inventories and
   agent reports) and the Wrappers 17/29 row; re-check the Loop/
   Primitives/Hardness member arithmetic you supplied; confirm the
   inclusion rule is applied symmetrically this time.
2. Verify the acknowledgment chain for R2-2 (ledger table + the plan's
   decision-log row) meets the template's debt disposition: named family,
   named owner, named window, human attribution.
3. Report in the standard table; findings verbatim into
   `audits/retrofit-r1-r3-findings.md`; the gate closes on zero blockers
   and majors, which retires epoch R1 and arms both 12.2c and RB4.

## Repository-side attestations

As rounds 1-2, unchanged (replays, axiom prints, lint, checksums,
bundles, shim exclusions, merge trail). This round's delta is
documentation only; no Lean source changed.
