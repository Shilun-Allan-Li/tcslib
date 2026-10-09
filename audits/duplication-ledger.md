# Cumulative duplication ledger

The standing per-file accounting of copied proved material that
`workflow.md` §4 requires at every epoch boundary (introduced as the
retrofit-R1 round-1 repair, finding R1-2 of
`audits/retrofit-r1-findings.md`). Updated at each integration that
creates, deletes, or re-homes copies; the epoch packs cite the current
state and the auditor verifies it.

**Counting convention.** The unit is a *source declaration that is a
member of a recorded byte-level twin correspondence* — the maps of
`audits/retrofit-inventory/{loop,primitives}.md` (produced 2026-10-09 by
comment/whitespace-normalized comparison) plus the A2/F2A reports'
declared copies. Each pair has an **original** side (the file that first
proved it) and a **copy** side (the file that re-derived it under the
fill-batch private-copy mechanism). Fractions are twin-member
declarations over the file's total declarations, and the line figures are
the inventories' docstring-inclusive block estimates. Disclosed
*design-harvest reimplementations* (re-derivations against the ABI with
the original as template, per `machine-library-design.md` §8 — e.g. the
Primitives P2 relocation layer from Loop's `emCall` family, and
`emitterCompare*` from `e3c*`) are listed separately: they are not
byte-level copies, and the construction-reuse policy governs them going
forward.

## State after retrofit epoch R1 (base `5588628c` → the merged PRs #9/#10)

| File | Total decls (final) | Twin members (original side) | Twin members (copy side) | Copied-material fraction (decls) | Approx lines in twin blocks | Disposition |
|---|---:|---:|---:|---:|---:|---|
| `Build/Loop.lean` | 212 (204 priv + 8 pub) | **87** (was 95; 8 dead originals deleted in RB1) | 0 | 41% | ≈ 2,350 of 5,515 | originals retained as the live loop engine; the Catalog copies collapse to one owner at **12.2c** (D-R2) |
| `Build/Primitives.lean` | 272 (254 priv + 18 pub) | **146** (was 150; 3 dead orphans + `catalogPair_inverse` deleted) | 0 | 54% | ≈ 3,300 of 6,374 | same 12.2c disposition; the four deleted originals' Catalog twins become sole owners or dead (below) |
| `Build/Catalog.lean` | 423 | 0 | **249** = 143 Primitives-sourced live pairs + 3 now-sole owners + 1 dead (`f2_catalogPair_inverse`-class) + 87 Loop-sourced live pairs + 8 dead Loop-twin copies + 17 Wrappers-sourced (10 `f2_timed*`, 7 `catalog_redirect*`) + 2 in-file `a2_` duplicates of `f2_` sum facts (approximate partition; the exact pair lists are the inventories') | 59% | ≈ 6,000 of 10,876 | **the 12.2c refactor's object**: per-theme files own each implementation once with time and space contracts; the 8 + 1 dead copies are dropped on sight; the `redirectTM` projection promotion rides along (F1 queue) |
| `Build/Wrappers.lean` | — | 17 (the `f2_timed*`/`catalog_redirect*` originals) | 0 | small | ≈ 450 | originals stay; copies collapse at 12.2c |
| `Build/Embed.lean`, `Build/Seam.lean`, `Build/VirtualInput.lean`, `Simulation.lean` | — | 0 | 0 | 0% | 0 | clean (the vhost-f1 and A-S1/A-S2 ledgers are "new copies: none", auditor-verified) |
| `CookLevin/Hardness.lean` | 549 | 0 cross-file | 0 | 0% cross-file | — | internal near-duplicates flagged by the inventory (`clCountTape ≡ bufferTape` noted; `clA5_pt_unaryLength` eliminated in RB3); the disclosed `emCall`-family design harvest is a reimplementation, not a copy |

**Epoch R1 delta**: new copies **0**; original-side twin members
95 + 150 = 245 → **233** (twelve dead originals deleted); one cross-file
Encoding duplicate pair (`catalogPair_inverse` ↔
`Turing.eq_pairEncode_of_pairDecode`) collapsed by the human-approved E1;
net lines −1,639, net private declarations −83 (76 dead + 7 eliminated by
replacement).

**Human-acknowledgment state**: the accumulated Catalog copy debt is
acknowledged and scheduled by the recorded decisions **D-R2** (12.2c
promoted to the next window after R1; precondition met) and **D-R3** (the
agreement-transfer lemma for the Loop-internal H3 duplication, landed as
§13 Z5 and proved in vhost-f1). No unacknowledged debt is known; any new
copy in a future delivery re-enters through the per-delivery ledger and
the one-fifth escalation rule of `workflow.md` §4.
