**Retrofit epoch R1 — round-4 external audit findings**

**Verdict: gate remains open — 0 blockers, 1 major, 2 minors, 7 notes.** The requested counter, Composition-private, and in-file reconciliations succeed. The listed union has exactly **289** Catalog declarations, with **283** strict normalized twins. However, the supplied Composition source reveals two further public strengthened correspondences: the identity and constant space theorems reproduce their original time proofs. Thus **289 is a verified subtotal**; the expanded census requires **at least 291/423 = 68.8%** in Catalog and **at least 5/19 = 26.3%** in Composition. The existing debt acknowledgments stand. No Lean correctness defect is asserted.

Evidence: the supplied `retrofit-r1-r4-bundle.md`, with ten attachments. Independently computed SHA-256: `e1bc46ba88ca93481bbf91c4d0fa4db7ea140cd0102a0bd7333a9b724004b70e`.

I extracted the three Lean sources; enumerated explicit source declarations with nested comments excluded; checked both agent inventories against Catalog; reconstructed the named partitions; compared the complete new private-family declarations under consistent identifier substitution and comment/whitespace removal; compared the counter and public time-proof adaptations; and sampled the remaining space material. Compiler-generated declarations are excluded. The earlier Loop/Primitives/Wrappers correspondence checks and retrofit freezes are carried from the attached round-3 findings: their original sources and patches are not attached here. No repository access, Lean invocation, or independent authentication of human actions was performed.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| R4-1 | **major** | `audits/duplication-ledger.md` · Catalog and Composition rows; `Composition.lean` · `computesFunInTime_id`, `computesFunInTime_const`; `Catalog.lean` · their `_spaceUsed` counterparts | The expanded census still omits two strengthened public correspondences. | After the outer existential/conjunction setup, **the entire remaining identity time proof** in Composition is normalized-identical to Catalog's time-conjunct proof; the same holds for the constant theorem. Both Catalog declarations add a space conjunct to the corresponding time result. Neither target nor either Composition original is in the listed union. The convention includes strengthened counterparts and already counts the analogous proof-body adaptation from `timeConstructible_id`; it states no public-target exclusion. Consequently Catalog requires at least `289 + 2 = 291` members, and Composition at least `3 + 2 = 5`. The additional pairs are excluded from the strict count. | Record both public correspondences on both sides and update expanded totals, percentages, and block spans. Screen the remaining public target proofs for the same form of substantial copied time proof, or explicitly qualify the census's coverage. Preserve D-R2/12.2c; this finding concerns incomplete accounting of existing material and requires no renewed human approval. |
| R4-2 | **minor** | Round-4 pack · “29 entries outside all partitions”; ledger reconciliation paragraph | The remainder and provenance labels are inaccurate, although the listed 289-member arithmetic works. | F2A's 254 inherited members are **150 Primitives + 94 Loop + 10 Wrappers**, not 254 Primitives/Loop members. Its 29-entry complement to those and the new external-copy blocks contains `f2_finSumEquiv` and `f2_sum_add`, which are already counted as in-file originals. Thus **27**, rather than 29, F2A declarations lie outside the full listed union. | State `306 = 150 + 94 + 10 + 3 + 20 + 2 + 27`. Describe the 29 as two counted originals plus 27 additional helpers. Update the plan's matching summary and the acknowledgment table's stale “264” family label when updating the ledger. |
| R4-3 | **minor** | Ledger · physical-line columns | Several line figures fail the stated docstring/closure-note span rule. | The listed counter/Composition additions occupy **345 + 51 = 396** Catalog lines, versus `≈320`. TimeConstructible's listed 20 members occupy **355** lines; Composition's listed three occupy **51**, versus `≈330` and `≈95`. Fresh counting also gives **2,200** for Catalog's Loop partition, rather than the carried 2,178: the 22-line docstring plus closure note before `f2_loopHost_contracts` is included by the rule. Full calculations appear below. | Replace estimates and the inherited omission with the measured spans. Include the additional public correspondences when expanding the member set. |
| R4-4 | note — no findings | Catalog / TimeConstructible · counter block | The requested **19 identical + 1 near-copy** reconciliation succeeds. | All 19 complete private counter declarations match under consistent `f2_` substitution. `f2_counter_computes` changes the outer theorem interface, then repeats exactly the proof tail of public `timeConstructible_id`. There is no source declaration named `counter_computes`. | Accept this reconciliation and attribution. |
| R4-5 | note — no findings | Catalog / Composition · listed private family; Catalog internal pairs | All three private Composition pairs and both internal pairs match. | `idTM`, `idTM_run`, and `constTM` match their `f2_` counterparts. `f2_finSumEquiv` ↔ `a2_mapSumEquiv` and `f2_sum_add` ↔ `a2_map_sum` match after simultaneous family-name substitution. Both sides of each internal pair are in the rebuilt union. | Accept these five comparisons and the internal-original repair. |
| R4-6 | note — no findings | Ledger · denominators and listed-member arithmetic | All three denominators and the listed 289/283 calculations reproduce. | Catalog has **423 = 384 private + 39 public** declarations; TimeConstructible **21 = 19 private + 2 public**; Composition **19 = 11 private + 8 public**. The disjoint listed Catalog groups total 289; removing the five historical strengthened targets and the counter near-copy leaves 283. TimeConstructible's 20/21 row passes. Composition's 3/19 is the correct listed-private subtotal, subject to R4-1. | Retain denominators and the verified subset evidence; update completeness claims as in R4-1. |
| R4-7 | note — no findings | `batchF2A2-REPORT.md` · R3-2 | The actual A2 report is now present, and its inventory reconciles. | All 45 unique inventory names occur in Catalog with the listed declaration kinds. Two are the internal copies and one is `a2_loop_halted_run`, already in the 95-member Loop partition. The other 42 are distinct from the listed member union. Samples of the forwarding controller, source-bank containment, source-radius proof, and segment composition support their construction roles. | Close R3-2. Carry the previously verified Loop provenance of `a2_loop_halted_run`. |
| R4-8 | note — no findings | Catalog · sampled F2A remainder | The sampled remainder contains substantive additional space machinery. | Samples include `f2_polyHeads`, `f2_poly_step`, `f2_poly_space`, all three counter-space additions, `f2_space_of_time`, `f2_segment_heads`, `f2_space_radius`, `f2_seamed_space`, and `f2_branch_space`. Their additional trajectory/cardinality obligations are visible in the statements and bodies; they are not unchanged copies of the attached counter or Composition declarations. The two known internal originals require the classification correction in R4-2. | Accept the sampled classifications at this evidence level; preserve the distinction between sampling and exhaustive comparison against unattached source files. |
| R4-9 | note — no findings | Ledger acknowledgment table; plan · D-R2/D-R3/RB4 | The substantive human debt dispositions remain adequate. | D-R2 assigns the per-theme consolidation to **12.2c, the next window after the RB batches**, with each implementation kept once alongside its time and space contracts. The user's recorded RB4 decision names the H3 and three-file relocation families, all three files, and **after the A-S1 fill gate closes**. These dispositions continue to cover the existing families; newly recognizing omitted members does not create a new implementation or debt event. | Carry the acknowledgments without renewed approval; synchronize the ledger's family labels with the corrected census. |
| R4-10 | note — no findings | R3-3 through R3-8 · carried closures and evidence boundaries | The requested Wrappers wording repair is present; earlier accepted source/debt findings remain carried. | The ledger now records **297 = 77 + 220** Wrappers lines. Wrappers itself is not reattached, so this is verification that the earlier measurement was adopted. The pack attests a documentation-only delta; no new retrofit patch is supplied. Nothing here reopens the prior deletion, freeze, E1, or RB4 disposition checks. | Close the original Wrappers estimate issue; retain R4-3 for the newly checked span discrepancies. Carry earlier closures at their recorded evidentiary level. Epoch R1 remains unretired while R4-1 is open. |

**Declaration-by-declaration counter comparison.**

Each of the following full declarations is identical after replacing all corresponding counter identifiers consistently with their `f2_` names and removing comments and whitespace. The numbers below are declaration start lines in the extracted source files.

| TimeConstructible original | Original line | Catalog counterpart | Catalog line |
|---|---:|---|---:|
| `counterInc` | 74 | `f2_counterInc` | 2858 |
| `counterCarry` | 80 | `f2_counterCarry` | 2864 |
| `counterInc_potential` | 86 | `f2_counterInc_potential` | 2870 |
| `counterInc_bits` | 98 | `f2_counterInc_bits` | 2882 |
| `counterInc_length` | 114 | `f2_counterInc_length` | 2898 |
| `counterBump` | 123 | `f2_counterBump` | 2907 |
| `counterTM` | 130 | `f2_counterTM` | 2914 |
| `counterTape` | 151 | `f2_counterTape` | 2935 |
| `counterCfg` | 155 | `f2_counterCfg` | 2939 |
| `counterTape_read` | 160 | `f2_counterTape_read` | 2944 |
| `counterTape_write` | 170 | `f2_counterTape_write` | 2954 |
| `counter_carry_step` | 191 | `f2_counter_carry_step` | 2975 |
| `counter_carry` | 216 | `f2_counter_carry` | 3000 |
| `counter_rewind` | 247 | `f2_counter_rewind` | 3031 |
| `counter_start` | 282 | `f2_counter_start` | 3066 |
| `counter_increment` | 311 | `f2_counter_increment` | 3095 |
| `counter_count` | 333 | `f2_counter_count` | 3117 |
| `counter_emit_run` | 362 | `f2_counter_emit_run` | 3146 |
| `counter_emit` | 390 | `f2_counter_emit` | 3174 |

For the twentieth member, TimeConstructible's `timeConstructible_id` starts at line 422 and Catalog's `f2_counter_computes` at line 3195. The source packages the lower-bound condition, coefficient 5, and `counterTM` into `TimeConstructible id`; the target exposes the concrete machine's `ComputesFunInTime` contract. Following that outer packaging, both have exactly the same normalized proof from `obtain ⟨t, ht, hc⟩` through the final `omega`. Counting this as an expanded member while excluding it from strict whole-declaration equality is correct.

The Composition-private start-line pairs are `idTM` 88 ↔ 1311, `idTM_run` 100 ↔ 1323, and `constTM` 168 ↔ 1358. All three complete comparisons pass. The two internal pairs start at 9962 ↔ 5331 and 9985 ↔ 5354, respectively; both complete comparisons pass.

**The two additional public correspondences.**

| Composition original | Catalog strengthened counterpart | Reproduced proof body |
|---|---|---|
| `computesFunInTime_id` | `computesFunInTime_id_spaceUsed` | Source lines 140–165 and Catalog lines 3757–3782 are identical after consistent `idTM`/`idTM_run` renaming and whitespace removal. The outer construction changes from one time obligation to time and space obligations; the additional space proof uses zero work tapes. |
| `computesFunInTime_const` | `computesFunInTime_const_spaceUsed` | Source lines 182–186 and Catalog lines 3800–3804 are identical after consistent `constTM` renaming and whitespace removal. Again the new conjunct is the zero-work-tape space bound. |

These are strengthened declarations containing the complete received time argument, exactly the sort of adaptation that the expanded metric can represent while keeping its strict metric separate. Merely adding a new conjunct does not remove that copied material. The supplied convention gives no exemption for public target bodies. The two omissions are outside both private-helper inventories, so exhaustively reconciling those inventories cannot establish whole-file completeness.

**Partition arithmetic.**

| Listed Catalog partition | Members |
|---|---:|
| Primitives | 150 |
| Loop | 95 = 94 F2A + 1 A2 |
| Wrappers | 17 = 10 F2A timed + 7 earlier redirect |
| In-file copy side | 2 |
| In-file original side | 2 |
| Composition private copies | 3 |
| Counter block | 20 |
| **Listed union** | **289** |

All listed names exist and the groups are disjoint. Therefore:

`150 + 95 + 17 + 2 + 2 + 3 + 20 = 289`.

`289 − 5 strengthened counterparts − 1 counter near-copy = 283`.

`100 × 289/423 = 68.3215%`; `100 × 283/423 = 66.9031%`.

The five historical strengthened targets are `f2_loopHost_prepare`, `f2_loopHost_contracts`, `f2_splitSolve_of_body`, `f2_splitSolve_source`, and `f2_splitSolve_closed`. Their classification is carried from the earlier source audit. The new public pairs increase only expanded membership:

`289 + 2 = 291`; `100 × 291/423 = 68.7943%`.

`291 − 7 strengthened counterparts − 1 counter near-copy = 283`.

TimeConstructible's expanded row is `19 + 1 = 20` of 21, giving `95.2381%`; its strict subtotal is 19 of 21. Composition's three exact private originals give `15.7895%`; adding the two public originals gives `5/19 = 26.3158%`. The two additions establish lower bounds on expanded completeness, pending the requested public-proof screen.

The private inventories reconcile separately:

`F2A: 306 = 150 + 94 + 10 + 3 + 20 + 2 in-file originals + 27 nonmembers`.

`A2: 45 = 2 in-file copies + 1 Loop copy + 42 nonmembers`.

`Listed Catalog union: 279 F2A + 3 A2 + 7 earlier redirect = 289`.

Thus the listed union leaves `423 − 289 = 134` declarations outside it, including all 39 public declarations. The two public proof correspondences above reduce that complement to at most 132.

**The 29-entry F2A complement and samples.**

These are the entries remaining after subtracting the 254 inherited copy-side entries, three Composition-private copies, and twenty counter members. F2A inventory numbers make the enumeration reproducible without assuming that every `f2_` name is a copy.

| Inventory entries | Names | Classification / sampled evidence |
|---|---|---|
| 58–62 | `f2_polyHeads`, `f2_polyHeads_bounds`, `f2_poly_step`, `f2_head_steps`, `f2_poly_space` | Additional head/trajectory machinery. The state-dependent predicate bounds active scanning and rewind heads; its preservation and interval-cardinality proof bound all-time space independently of loop count. |
| 83–85 | `f2_counter_count_space`, `f2_counter_heads`, `f2_counter_space` | Additional space obligations. The first extends the counting invariant to every intermediate prefix; the next covers emission and halted tails; the last takes the visited interval's cardinality. The received `counter_count` alone has no prefix-head conclusion. |
| 99–101 | `f2_space_of_time`, `f2_unary_sharp`, `f2_first_length` | Space-transfer and supporting bounds. Sampled `f2_space_of_time` contains all later visited positions in the halted time-prefix image before summing cardinalities. The other two are time/length auxiliaries, rather than standalone space statements. |
| 116 | `f2_strip_linear` | A sharper assembled time bound used to obtain space; included among the additional auxiliaries. |
| 208 | `f2_loopCall_heads` | A canonical-call head bound: the retained fuel bank supplies the displacement, while the other canonical heads are at their origins. |
| 212–215 | `f2_segment_heads`, `f2_space_radius`, `f2_seamed_space`, `f2_exists_loopFind_space` | Additional interval, cardinality, and loop-space composition. The sampled segment lemma bounds every trace from bounded seams and segment lengths; the number of rounds does not multiply its radius. |
| 295–297 | `f2_cond_time`, `f2_rewind_scan_heads`, `f2_rewind_heads` | Time assembly and rewind-head auxiliaries. The rewind additions retain equality of work-head positions throughout the administrative trace. |
| 298–299 | `f2_finSumEquiv`, `f2_sum_add` | **Already counted originals** of the two exact A2 copies. These are the reason “29 outside all partitions” is false. |
| 300–306 | `f2_branch_space`, `f2_condHeads`, `f2_control_heads`, `f2_branch_heads`, `f2_read_heads`, `f2_cond_ledger`, `f2_cond_space` | Additional conditional-bank accounting. Sampled `f2_branch_space` splits selected-source visited space from the unselected bank's origin cells; the head-layout and prefix ledger supply the conditional space bound. |

The A2 sample also supports its declared roles: `a2_mapTM` has two administrative buffers plus the payload work bank and directly forwards payload output; `a2_mapVirtual` preserves the source work tapes and head positions; `a2_map_space` consumes per-tape visited-set containment and charges the two buffers separately. `a2_source_radius` derives head displacement from a source-space bound by unit-step interval coverage. `a2_segments` reuses a common interval across successive segments. These are substantive additions; this sample is not a claim of exhaustive novelty against every repository file.

**Physical-line recomputation.**

The rule counts each member from its attached docstring, including an intervening closure note, through its last code line. Separating blank lines and module notes are excluded.

| Catalog listed group | Measured lines |
|---|---:|
| Primitives | 3,249 |
| Loop | 2,200 |
| Wrappers | 297 |
| Two internal copies | 30 |
| Two internal originals | 30 |
| Three Composition-private copies | 51 |
| Twenty counter members | 345 |
| **Listed 289-member union** | **6,202** |

The Loop discrepancy is exactly 22 lines: Catalog lines 7615–7633 contain the attached `f2_loopHost_contracts` docstring, and lines 7634–7636 its closure note. Omitting all 22 reproduces the carried 2,178 and 5,754 subset measurements. Including them gives the earlier 264-member subset **5,776** lines. Hence:

`5,776 + 30 + 51 + 345 = 6,202`.

The two public Catalog counterparts occupy 44 and 21 docstring-inclusive lines, so the known 291-member expansion occupies **6,267** lines.

TimeConstructible's nineteen counter-original spans sum to 315 lines; `timeConstructible_id` contributes 40, giving **355**. Composition's three private spans are `11 + 35 + 5 = 51`; its two public spans are `32 + 14 = 46`, giving **97** for the five-member expansion. Wrappers' adopted **297 = 77 + 220** remains correct; Catalog's corresponding spans independently reproduce that total.

**Disposition.** R3-1's specifically named omissions are repaired, and R3-2 and the original Wrappers estimate issue close. R4-1 keeps the cumulative-completeness gate open. The required next action is a consistent expanded ledger that includes the two public proof correspondences and checks the remaining public targets for the same pattern. D-R2, D-R3, and RB4 remain acknowledged at the packet's established evidentiary level; this audit neither renews their approval nor certifies the separate A-S1 fill gate closed.
