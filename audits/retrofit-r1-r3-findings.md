**Retrofit epoch R1 — round-3 external audit findings**

**Verdict: gate remains open — 0 blockers, 1 major, 2 minors, 5 notes.** R2-2 is closed: the required human acknowledgment names the families, RB4 as owner, and the resolution window. R2-3 is closed. R2-1 remains open: the rebuilt Catalog row correctly counts its listed copy-side subset, but still does not implement its stated symmetric membership rule or account for all declared copies. No Lean correctness defect is asserted.

Evidence: the supplied `retrofit-r1-r3-bundle.md`, containing 15 attachments. Independently computed bundle SHA-256: `b7ba3df87f3d46bf28f5829f318369415c1bd23f0f497ae780dcefef9d682755`.

I extracted and enumerated the two attached Lean files with nested comments excluded; reconstructed all 264 listed Catalog memberships from the inventories and source names; checked distinctness; compared all 17 Wrappers correspondences and both internal pairs after consistent identifier substitution and comment/whitespace removal; and checked the acknowledgment records. Counts concern explicit source declarations, including named instances, rather than generated kernel declarations. The three original retrofit source files and their patches are not reattached this round: their previously audited counts, equality checks, and freezes are carried from the attached round-2 findings, not claimed as fresh source comparisons. No Lean build, repository access, or independent authentication of human actions was performed.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| R3-1 | **major** | `audits/duplication-ledger.md:18–31, 41` · Catalog membership; R2-1 | The Catalog total remains incomplete under the ledger's own rule. | The listed `150 + 95 + 17 + 2 = 264` members exist and are disjoint. However, the two internal pairs contribute **four** declarations: `f2_finSumEquiv` ↔ `a2_mapSumEquiv` and `f2_sum_add` ↔ `a2_map_sum`. Both pairs are normalized-identical; neither `f2_` original occurs in the 264. Thus the existing recorded correspondences already require **266** members, not 264, and Catalog's original-side column cannot be zero. The F2A report and Catalog's source additionally declare omitted Composition copies (`f2_idTM`, `f2_idTM_run`, `f2_constTM`) and copied counter material, including the explicitly attributed `f2_counter_computes`. These are outside all four printed groups. | Regenerate the ledger from the union of both sides of each recorded correspondence, counting each distinct declaration once per file. Retain 264 only as the identified copy-side subset. Add the omitted internal originals and declared external-copy families; supply counterpart mappings/evidence for the counter block and the corresponding original-side rows. Recompute complete totals and strict counts. Carry D-R2's existing 12.2c disposition; this is not a request to reapprove accepted debt. |
| R3-2 | **minor** | Round-3 pack · R2-1 disposition; attachment inventory | The promised A2 report is absent. | The three report attachments are `batchF2A-REPORT.md`, retrofit `rb2-REPORT.md`, and vhost `f1-REPORT.md`. The latter two are not the Catalog continuation A2 report. Catalog contains 45 `a2_` declarations. Its source suffices to verify the two internal pairs and the mapped `a2_loop_halted_run`, so this omission does not independently undo those checks. | Attach the actual Catalog A2 report, or correct the attachment claim and replace its cited provenance with a complete correspondence manifest. |
| R3-3 | **minor** | `audits/duplication-ledger.md:42` · Wrappers line estimate | The approximately 450-line estimate is not reproduced by the stated span rule. | The 17 member spans total **297** physical lines, including attached docstrings and internal blank/comment lines and excluding separating blanks/module notes. The identical Catalog counterparts also total 297. The two portions are 77 redirect lines and 220 timed-controller lines. | Replace `≈450` with 297, or document a genuinely different attribution rule and apply it consistently. |
| R3-4 | note — no findings | Catalog / Wrappers · listed partitions and strengthened rows | The previously conditional listed partitions and both denominators are now independently reproducible. | Catalog has **423 = 384 private + 39 public** source declarations; Wrappers has **29 = 19 private + 10 public**. Catalog's listed subset is **150 + 95 + 17 + 2 = 264**. The five strengthened historical counterparts are all present and included on both sides of their historical maps. All 17 Wrappers pairs are normalized-identical; **17/29 = 58.6%**. The omitted originals in R3-1 are additional to this verified subset. | Accept these subset counts and the Wrappers declaration fraction. Do not treat the subset as the complete Catalog total. |
| R3-5 | note — no findings | Loop / Primitives / Hardness · corrected named-family arithmetic | The repaired arithmetic correctly includes the previously omitted relocation and H3 members. | Re-enumeration of the inventory maps gives 95 Loop and 150 Primitives originals. With the round-2 verified removals, Loop contributes `(95 − 8) + 4 + 13 = 104`; Primitives contributes `(150 − 4) + 4 = 150`; Hardness contributes 4. The denominators carried from the round-2 source audit give **49.1%, 55.1%, 0.73%**. H3's originals are already in the 87 and are not counted twice; the explicitly excluded `_init` near-copy remains disclosed. | Accept these corrected named-family rows, preserving the distinction between carried source evidence and this round's recomputed arithmetic. |
| R3-6 | note — no findings | Ledger acknowledgment table; plan §4d decision log · R2-2 | The debt acknowledgment satisfies the template and closes R2-2. | The plan's final **Decided** row, attributed to the **user, 2026-10-09**, names the 13 H3 copies and the three-file relocation family; assigns **RB4** over Loop, Primitives, and Hardness; and sets the window **after the A-S1 fill gate closes**. The ledger agrees: H3 uses Z5; relocation uses the selected-tape exports plus Z5. “The same RB4” in the relocation row inherits the stated window, and the plan states it explicitly. The earlier pending proposal is superseded by this decision. | Close R2-2. Carry D-R2/D-R3 and their existing dispositions without renewed approval. This accepts the recorded acknowledgment at the packet's established evidentiary level. |
| R3-7 | note — no findings | Ledger epoch delta · R2-3 | The corrected deletion wording and arithmetic pass. | Historical-map removals are `8 + 3 = 11` dead originals plus the one live `catalogPair_inverse` eliminated by replacement: `245 − 11 − 1 = 233`. The separately audited epoch-wide totals remain `76 + 7 = 83` removed privates and 1,639 removed lines. | Close R2-3; retain both distinctions. |
| R3-8 | note — no findings | R2-4–R2-11 · carried closures and evidence boundaries | Nothing in the supplied documentation repair warrants reopening the earlier source, E1, deletion, or strict-simplification findings. | The pack declares a documentation-only delta. The attached round-2 report records the exact reconstruction, public freezes, E1 proposition comparison, replacement checks, and limitations of the kernel/merge evidence. This round contains neither a new retrofit patch nor evidence contradicting those results. | Carry the earlier closures and no-findings rows at their recorded evidentiary level. Do not describe this audit as a fresh patch replay or kernel check. |

**Catalog partition recomputation.**

The Primitives inventory's F01–F10 sizes are

`5 + 7 + 3 + 3 + 4 + 12 + 20 + 11 + 1 + 14 = 80`.

Its F13–F22 sizes are

`9 + 5 + 9 + 7 + 1 + 8 + 6 + 12 + 6 + 6 = 69`.

Adding `catalogPair_inverse` gives `80 + 69 + 1 = 150`. Each name has exactly one `f2_` counterpart in the attached Catalog.

The Loop inventory's F1–F15, retaining its separately listed F7b, give

`9 + 10 + 2 + 6 + 6 + 3 + 12 + 4 + 9 + 7 + 9 + 5 + 2 + 5 + 4 + 2 = 95`.

Exactly 94 use the `f2_` prefix; the exception is `loop_halted_run` → `a2_loop_halted_run` (Catalog:10667). Therefore the listed Catalog partition can also be checked directly by prefix and provenance:

`150 f2_Primitives + 94 f2_Loop + 1 a2_Loop + 10 f2_timed + 7 catalog_redirect + 2 a2_internal = 264`.

All 264 names are distinct. Every one of the F2A report's 306 inventory entries exists in Catalog. Of these, 254 are in the listed partition; **52 are outside it**. Those 52 are not all copies: they also contain new space proofs, so treating every `f2_` declaration as copied would overcount. The copy classification must be made declaration by declaration.

The five strengthened counterparts are `f2_loopHost_prepare`, `f2_loopHost_contracts`, `f2_splitSolve_of_body`, `f2_splitSolve_source`, and `f2_splitSolve_closed`. For the listed subset, the ledger's secondary arithmetic is consequently

`264 − 2 − 3 = 259`, and `100 × 259/423 = 61.2293%`.

This confirms the arithmetic of the secondary subset, not a fresh comparison against the unprovided Loop/Primitives originals and not a complete strict-twin Catalog total.

**The internal-pair counterexample to completeness.**

| Original in Catalog | Copy in Catalog | Original declaration line | Copy declaration line | Comparison |
|---|---|---:|---:|---|
| `f2_finSumEquiv` | `a2_mapSumEquiv` | 9962 | 5331 | Identical after the two consistent family-name substitutions and normalization |
| `f2_sum_add` | `a2_map_sum` | 9985 | 5354 | Identical under the same substitutions and normalization |

The first declaration builds the finite-sum indexing equivalence; the second uses it to split the sum. Both originals and both copies are present. The two original names are absent from the 150/95/17/2 lists. Applying “each member once per file” therefore gives

`150 + 95 + 17 + 4 = 266`, and `100 × 266/423 = 62.8842%`.

This is an unconditional lower bound from the already recorded correspondences, independent of any further copy classifications. It alone prevents closure of R2-1.

**Additional declared copies omitted by the partition.**

| Catalog material | Attached provenance | Accounting consequence |
|---|---|---|
| `f2_idTM` (1311), `f2_idTM_run` (1323), `f2_constTM` (1358) | Catalog:1305–1307 explicitly calls these local Composition/Primitives witness copies with unchanged transition tables and time proofs except for the prefix; F2A report:162 names Composition among the received copy sources. They are not members of the enumerated Primitives map. | Three additional declared-copy members. The matching Composition source is not attached, so exact source equality is not independently certified here. |
| `f2_counter_computes` (3195) | Its docstring at Catalog:3191–3194 explicitly attributes the complete time proof to `ClassP/TimeConstructible.lean`; the F2A report:162 likewise declares the counter implementation and amortized arithmetic copied. | At least this further declaration requires inclusion under the declared-copy rule; its provenance cannot be silently omitted. |
| F2A inventory entries 63–82, from `f2_counterInc` through `f2_counter_computes` | Twenty declarations form the counter implementation/time-proof block, Catalog:2858–3220. The subsequent entries 83–85 are its space additions. | Reconcile the twenty individually against the stated source, rather than count none of the block or assume all 23 `f2_counter*` declarations are exact copies. |

Counting just the four individually identified declared copies above, in addition to the internal-original repair, gives a declared-membership lower bound of

`264 + 2 + 3 + 1 = 270`, and `100 × 270/423 = 63.8298%`.

If all twenty counter implementation/time-proof declarations have the reported copied provenance, the corresponding subtotal is `264 + 2 + 3 + 20 = 289`, or `68.3215%`. **289 is a conditional subtotal, not a certified complete total.** The absent original counter source and absent A2 report preclude certifying completeness from those reports alone. The final ledger should also identify the original-side members and denominators for any additional source files it includes.

**Wrappers recomputation and exact span counts.**

All names below occur in Wrappers and in Catalog under the indicated prefix. All 17 complete declarations match after simultaneous prefix substitution and comment/whitespace normalization.

| Wrappers member | Catalog prefix | Docstring-inclusive Wrappers span | Lines |
|---|---|---|---:|
| `redirectState` | `catalog_` | 335–341 | 7 |
| `redirectAction` | `catalog_` | 343–346 | 4 |
| `redirectCfg` | `catalog_` | 348–354 | 7 |
| `redirect_loop` | `catalog_` | 356–365 | 10 |
| `redirect_apply` | `catalog_` | 367–377 | 11 |
| `redirect_step` | `catalog_` | 379–407 | 29 |
| `redirect_run` | `catalog_` | 409–417 | 9 |
| `timedPadTM` | `f2_` | 468–472 | 5 |
| `timedCondTM` | `f2_` | 474–501 | 28 |
| `timedBranchCfg` | `f2_` | 503–510 | 8 |
| `timedControlCfg` | `f2_` | 512–518 | 7 |
| `timed_capture` | `f2_` | 520–535 | 16 |
| `timed_control_init` | `f2_` | 537–554 | 18 |
| `timed_branch_run` | `f2_` | 556–591 | 36 |
| `timedReadyCfg` | `f2_` | 593–600 | 8 |
| `timed_read` | `f2_` | 602–657 | 56 |
| `timed_start` | `f2_` | 659–696 | 38 |

Thus `7 + 10 = 17` members, `10 + 19 = 29` declarations, and `100 × 17/29 = 58.6207%`. The seven redirect spans total 77 lines; the ten timed spans total 220; `77 + 220 = 297`.

For the Catalog subset of 264, the same span rule gives `3,249 + 2,178 + 297 + 30 = 5,754` lines (Primitives, Loop, Wrappers, internal copies respectively). The omitted internal originals add 30 lines. These are subset measurements. The old original-side measurements of 2,009 Loop lines, 3,162 Primitives lines, and 73 relocation lines per file remain carried round-2 measurements; the relevant full originals are not attached here.

**Original-side arithmetic and epoch delta.**

| File | Recomputed named-family arithmetic | Denominator from source audit | Percentage |
|---|---|---:|---:|
| Loop | `95 − 8 = 87`; `87 + 4 + 13 = 104` | 212, carried round 2 | `100 × 104/212 = 49.0566%` |
| Primitives | `150 − 4 = 146`; `146 + 4 = 150` | 272, carried round 2 | `100 × 150/272 = 55.1471%` |
| Hardness | `4` relocation copies | 549, carried round 2 | `100 × 4/549 = 0.7286%` |

The relocation family contributes `4 × 3 = 12` distinct declarations across the three files. H3 adds 13 copies in Loop, with the corresponding originals already counted in its 87. The expressly uncounted `_init` near-copy is not silently added to these totals.

The attached Catalog reference graph also supports keeping deleted-original counterparts in the accounting: the eight Loop counterparts have no referrers outside their deleted-original counterpart set; the three split orphans have no referrers; but `f2_catalogPair_inverse` is referenced by **both** `f2_first_length` and `f2_strip_linear`. These are source-token checks with comments excluded, not kernel reachability certification. No member is subtracted merely because its original was removed or its own code is dead.

The historical maps reconcile as `95 + 150 = 245`, `(95 − 8) + (150 − 4) = 87 + 146 = 233`, and `245 − 233 = 12 = 11 dead + 1 replaced`. Separately, the whole epoch removed `76 + 7 = 83` privates and `198 + 1,262 + 179 = 1,639` lines, as recorded by round 2.

**Acknowledgment disposition.** The plan's explicit RB4 decision supersedes its preceding pending proposal. Together with the ledger, it covers both R2-2 families, all three relocation files, the named owner, the window, and human attribution. D-R2's 12.2c assignment and D-R3's prior H3 acknowledgment continue to stand. The remaining gate issue is accurate cumulative accounting, not missing RB4 consent. This round does not retire epoch R1 or certify the separate A-S1 fill gate closed.
