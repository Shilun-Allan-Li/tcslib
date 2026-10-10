# Chapter-1/2 retrofit epoch R1 — round-5 findings

**Gate: OPEN — 0 blockers, 2 majors, 1 minor.** The two reported Composition hits, the listed 291/283 census, and its physical spans reproduce. The claim that the census is complete does not: a substantial public-to-private proof adaptation remains uncounted, and the stated public-proof screen has six additional hits. R4-1 is not discharged. Epoch R1 is not retired by this audit; its gate does not arm 12.2c. The separately recorded A-S1 closure and RB4 acknowledgment remain valid.

Audited the supplied `retrofit-r1-r5-bundle.md`, SHA-256 `2b6e739d344e009cef8ba82c9ff0090857a127b489fd6a0eded5efc4937c5492`. All source locations below refer to the extracted attachment, not bundle line numbers. This is a documentation/debt audit; proof scripts are compared as evidence of correspondence, not rechecked for logical correctness.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| R5-1 | **major** | `audits/duplication-ledger.md` · 27 F2A nonmembers; `Build/Catalog.lean` · `f2_strip_linear`; `Build/Primitives.lean` · `computesFunInTime_stripLast` | A substantial public-proof adaptation is still outside both sides of the ledger. | Catalog lines 4495–4558 reproduce the marker-stripper time argument from Primitives lines 2812–2880, retaining a linear bound. After consistent `f2_` renaming, **the entire proof becomes identical after just five localized edits**, itemized below. The largest unchanged contiguous proof block is 706 normalized characters. `f2_strip_linear` is explicitly among the claimed 27 nonmembers; the public source is outside Primitives' 150-member union. The linear strengthening does not exempt this correspondence from the expanded rule, just as the previously accepted counter adaptation and public space strengthenings are not exempt. | Record the correspondence on both sides, excluding it from strict whole-declaration equality. At minimum Catalog becomes **292/423 = 69.0%, 6,331 lines** and Primitives **151/272 = 55.5%, 3,316 lines**; the known Catalog strict subtotal stays 283. Reclassify this F2A entry and synchronize the acknowledgment label, exclusion explanation, pack, and current plan summary. Screen moved time proofs in the residual helpers, as well as direct public counterparts. This is additional accounting of existing D-R2 debt, not a new implementation or renewed approval request. |
| R5-2 | **major** | Ledger · “The public-proof screen”; round-5 pack · R4-1 disposition; plan · latest retrofit decision row | “Exactly two hits; all Primitives rows distinct” does not reproduce under the stated ≥60-character contiguous-reproduction screen. | The two Composition hits reproduce, but **six additional Primitives pairs** contain normalized contiguous matches of **62, 75, 75, 75, 91, and 121 characters**, all inside the Catalog time arguments. They are `prepend`, `pairFst`, `pairSnd`, `pairConcat`, `pairLenCheck`, and `stripLast`; exact locations and segments appear below. All six Catalog public targets are outside the listed 291-member union. Enumerating every source 60-character window independently confirms the same hit set. The stated qualification about *below-threshold* adaptation does not explain these above-threshold matches. | Publish the actual per-pair candidate results and a separate disposition for each match. Short arithmetic/parse fragments need not automatically become whole-declaration debt members, but any boilerplate or partial-overlap exclusion must be explicit, reproducible, and distinguished from “no hit.” Correct the pack and plan accordingly. Do not certify that no screen hit is outside the ledger while these six are unrecorded. |
| R5-3 | **minor** | Ledger, pack, and plan · “16 screened Primitives rows” | The stated population has 15 eligible Primitives rows, not 16. | Primitives declares 18 public `computesFunInTime_*` theorems. Exactly 15 have the named Catalog `_spaceUsed` counterpart. `splitSolveWith`, `unaryToken`, and `appendBit` do not. Composition contributes two eligible rows, giving **17 pairs total**. Catalog also has `computesFunInTime_cond_spaceUsed`, but neither attached Composition nor Primitives declares `computesFunInTime_cond`; it cannot silently supply a sixteenth Primitives row. | Correct the count to 15 and enumerate the population, or identify the intended extra source theorem and amend the source scope/evidence. |
| R5-4 | note — no findings | Composition · `computesFunInTime_id`, `computesFunInTime_const`; Catalog · their `_spaceUsed` counterparts | Both demanded public correspondences are correctly recorded on both sides. | After existential/conjunction setup, Composition lines 140–165 and 182–186 match Catalog lines 3757–3782 and 3800–3804 under consistent helper renaming and comment/whitespace removal: 776 and 273 normalized characters. The added space conjuncts use zero work tapes. The targets are expanded members and strict exclusions; the source row correctly has five expanded members and three strict members. | Accept this part of R4-1's repair. |
| R5-5 | note — no findings | Ledger · listed census, denominators, reconciliation, physical spans | The arithmetic is correct for the **listed** member set. | Fresh declaration counts give Catalog 423 = 384 private + 39 public, Primitives 272 = 254 + 18, Composition 19 = 11 + 8, and TimeConstructible 21 = 19 + 2. The disjoint listed Catalog groups total 291; deleting seven strengthened targets and the counter near-copy gives 283. Their spans total 6,267, including Loop 2,200 and counter 345. Composition gives 97 = 51 + 46; TimeConstructible gives 355. Details below. | Retain the measurements as verified subtotals, then incorporate R5-1 and adjudicate R5-2. Correct arithmetic does not establish completeness. |
| R5-6 | note — no findings | Catalog / TimeConstructible / Composition · private correspondences; Catalog internal pairs | The previously verified core correspondences reproduce. | Repeated all 19 complete counter comparisons, the counter adaptation's proof-tail comparison, the three complete Composition-private comparisons, and both internal pairs. All pass. In the attached Primitives source, 146 surviving private counterparts are found: 143 whole-declaration normalized matches and the same three known `splitSolve` strengthenings. | Carry these closures. |
| R5-7 | note — no findings | Catalog · sampled direct-screen no-hits | Several sampled no-hits have the stated substantive differences, but “no hit” is not a novelty certificate. | `lengthBits` switches from unpacking `timeConstructible_id` to the concrete counter with a space theorem. `polyBits` separates zero coefficient/exponent and uses the sharper assembled witness; its longest direct match is 25 characters. `pairMapSnd` uses the A2 forwarding controller and coefficient-one source-space accounting instead of the received capture/replay controller; its longest match is 30. Conversely, `splitSolve` has an **identical normalized 27-character citation proof**, below the threshold. | Keep the threshold-qualified verdicts; describe new trajectory obligations and reused time material separately. |
| R5-8 | note — no findings | Ledger acknowledgment table; plan · D-R2, D-R3, RB4 | The prior debt acknowledgments remain adequate; the old 264 label was updated to the listed 291 census. | The table names the expanded Catalog family, D-R2, and 12.2c, and retains RB4's H3/three-file relocation scope and A-S1-close window. The attached plan records A-S1 fill-gate closure and issuance of the RB4 brief. Recognizing another existing member does not create a new implementation or debt event. | Carry approvals and scheduling decisions. Update the family label with the corrected census; this audit does not undo RB4's independently recorded open window. |
| R5-9 | note — no findings | Round-5 documentation-only attestation; carried round-4 closures | No new Lean change is proposed; earlier source/deletion/freeze closures are carried at their established evidence level. | This packet supplies current sources and the round-4 report, but not prior source blobs or a round-5 patch. Therefore documentation-only history and separate-gate closure are repository-side attestations, not fresh byte-diff/kernel checks in this audit. Earlier Loop/Wrappers/Hardness provenance and the A2 report remain carried where their original evidence is not reattached. | Preserve these evidence boundaries. No Lean edit or new human acknowledgment is needed to resolve the findings above. |

**Screen reproduction.** Extract top-level declarations from comment-masked Lean text, retaining nested-comment handling and line positions. Select each public source name beginning `computesFunInTime_` for which Catalog declares that exact name followed by `_spaceUsed`. Extract proof bodies after the theorem's `:= by`; consistently rename source helper identifiers to existing `f2_` counterparts and remove whitespace. For the candidate pass, find common contiguous segments of at least 60 Unicode characters. A longest-common-substring calculation and an independent enumeration of all 60-character source windows agree on every verdict. Every positive segment was then located within the target's time argument; none of the additional positives depends on a statement, docstring, or space-conjunct match. Scanning whole target proof bodies for candidates is conservative for no-hits and does not enlarge the final positive set, since all eight positive maxima lie in the time arguments.

The table uses theorem-name suffixes only; every source name is `computesFunInTime_` followed by the suffix, and every target adds `_spaceUsed`.

| Source file | Suffix | Source declaration line | Catalog declaration line | Longest normalized common segment | Literal ≥60 verdict |
|---|---|---:|---:|---:|---|
| Composition | `id` | 137 | 3750 | 776 | hit, recorded |
| Composition | `const` | 179 | 3793 | 273 | hit, recorded |
| Primitives | `prepend` | 2096 | 3818 | 62 | **hit, unrecorded** |
| Primitives | `lengthBits` | 2111 | 3842 | 6 | no hit |
| Primitives | `polyUnary` | 2133 | 3859 | 44 | no hit |
| Primitives | `polyBits` | 2157 | 3901 | 25 | no hit |
| Primitives | `pairEncodeFixed` | 2194 | 3971 | 51 | no hit |
| Primitives | `pairFst` | 2209 | 3989 | 75 | **hit, unrecorded** |
| Primitives | `pairSnd` | 2228 | 4014 | 75 | **hit, unrecorded** |
| Primitives | `pairValid` | 2245 | 4039 | 32 | no hit |
| Primitives | `pairConcat` | 2261 | 4059 | 75 | **hit, unrecorded** |
| Primitives | `pairDup` | 2282 | 4087 | 35 | no hit |
| Primitives | `pairMapSnd` | 2715 | 5425 | 30 | no hit |
| Primitives | `pairLenCheck` | 2751 | 4139 | 91 | **hit, unrecorded** |
| Primitives | `stripLast` | 2812 | 4573 | 121 | **hit, unrecorded** |
| Primitives | `splitSolve` | 4312 | 9517 | 27 | no hit; entire short citation matches |
| Primitives | `incFixed` | 4333 | 4611 | 37 | no hit |

Thus the literal screen produces **2 Composition hits + 6 Primitives hits + 9 Primitives no-hits = 17 pairs**. The five unmatched source theorems are Composition's `ifEq`/`comp` and Primitives' `splitSolveWith`/`unaryToken`/`appendBit`.

**Six unrecorded direct-screen segments.** These matches are unaffected by any ambiguity in helper renaming: the segments themselves contain no renamed helper.

| Pair | Primitives lines | Catalog lines | Shared fragment and interpretation |
|---|---|---|---|
| `prepend` | 2100–2101 | 3826–3827 | The complete arithmetic tail `simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]` followed by `omega` — 62 normalized characters. |
| `pairFst` | 2215–2217 | 3999–4001 | The three-line `cases hd : pairDecode x with` / `none` / `some p` proof tail — 75 characters. Catalog increases the time coefficient before retaining this parse-result case split. |
| `pairSnd` | 2234–2236 | 4024–4026 | The same 75-character parse-result proof tail. |
| `pairConcat` | 2270–2272 | 4072–4074 | The same 75-character parse-result proof tail. |
| `pairLenCheck` | 2779–2781 | 4194–4196 | The 91-character suffix beginning `:= by simpa only [Nat.pow_one]` and ending `(show 1 ≤ e + 1 by omega)`. Source abbreviates the right side as `P`; target writes the power explicitly. |
| `stripLast` | 2873–2875 | 4589–4591 | The full local proof `have hn : x.length + 1 ≤ (x.length + 1) ^ 2 := by ...` — 121 characters. Both use it for the deliberate quadratic weakening. |

These are candidates under the published screen, not six automatic findings of wholesale duplication. A revised ledger may distinguish incidental/common tactic fragments, retained short proof tails, and substantial adaptations. It must give those dispositions instead of reporting that no match occurred.

**The omitted substantial adaptation.** `f2_strip_linear` has the same marker-stripping function as `computesFunInTime_stripLast`, with linear rather than quadratic time. Its 64-line declaration has no attached docstring. Starting with the source proof and performing the advertised consistent `f2_` helper renaming, the following five edits produce the target's entire normalized proof exactly:

1. Unpack `computesFunInTime_pairSnd_spaceUsed`, adding the ignored space field, instead of `computesFunInTime_pairSnd`.
2. Unpack `computesFunInTime_const_spaceUsed`, likewise adding the ignored space field, instead of `computesFunInTime_const`.
3. Replace `Turing.eq_pairEncode_of_pairDecode` with `f2_catalogPair_inverse`, the already accounted inverse counterpart.
4. Delete the local `have hn` proving the linear input factor is bounded by its square.
5. Delete the final calculation's use of `hn` to weaken the linear bound to the quadratic bound.

Everything else is identical after normalization: the composition/conditional setup, the marker cases, the witness coefficient, the output proof, and the entire linear bound calculation. This is substantially stronger evidence than a common short tactic suffix. Its source is a public declaration and its target is private, so a screen restricted to equally named public `_spaceUsed` declarations misses it.

A coverage follow-up compared the attached public proofs with the 27 claimed F2A nonmembers. Besides the 706-character block in `f2_strip_linear`, a 215-character block occurs between `timeConstructible_id` and `f2_counter_heads`. That latter match belongs to the counter's emission-entry transition calculation amid additional all-prefix space obligations; it is a partial-reuse candidate for explicit disposition, not a basis here for automatically counting another whole declaration. No claim of exhaustive novelty is made for the residual helpers or for unattached repository files.

**Census and spans.** The following reconstructs the packet's listed union, before incorporating R5-1.

| Catalog partition | Members | Docstring/closure-note-inclusive lines |
|---|---:|---:|
| Primitives-sourced | 150 | 3,249 |
| Loop-sourced | 95 | 2,200 |
| Wrappers-sourced | 17 | 297 |
| In-file originals | 2 | 30 |
| In-file copies | 2 | 30 |
| Composition private copies | 3 | 51 |
| Counter block | 20 | 345 |
| Composition public counterparts | 2 | 65 |
| **Listed union** | **291** | **6,267** |

The membership reconstruction uses the round-4 report's explicit 27-name F2A remainder, the current 306 `f2_` declarations, the three counted A2 declarations, seven earlier redirect declarations, and the two public additions. All listed names exist and the groups are disjoint. The current Primitives file independently supplies 146 surviving private counterparts; the four historical deleted counterparts are carried from the accepted reconciliation. Loop and Wrappers source provenance is carried, while their Catalog member spans are recounted directly.

The arithmetic is:

```text
150 + 95 + 17 + 2 + 2 + 3 + 20 + 2 = 291
291 − 7 strengthened counterparts − 1 counter near-copy = 283
100 × 291 / 423 = 68.794326...% → 68.8%
100 × 283 / 423 = 66.903073...% → 66.9%

306 = 150 + 94 + 10 + 3 + 20 + 2 + 27
45 = 2 internal copies + 1 Loop copy + 42 nonmembers
291 = 279 F2A + 3 A2 + 7 earlier redirect + 2 public

3,249 + 2,200 + 297 + 30 + 30 + 51 + 345 = 6,202
6,202 + 44 + 21 = 6,267
Wrappers spans: 77 + 220 = 297
TimeConstructible spans: 315 + 40 = 355
Composition spans: (11 + 35 + 5) + (32 + 14) = 97

100 × 5 / 19 = 26.315789...% → 26.3%
100 × 3 / 19 = 15.789473...% → 15.8%
100 × 20 / 21 = 95.238095...% → 95.2%
100 × 19 / 21 = 90.476190...% → 90.5%
```

The 2,200-line Loop measurement includes the 22 lines at Catalog 7615–7636 before `f2_loopHost_contracts`, as required. Composition's public targets occupy 44 and 21 Catalog lines. This closes the named R4-3 measurement corrections, without converting the listed totals into a completeness certificate.

Accounting for **R5-1 alone**, before deciding how to classify the other overlap candidates:

```text
Catalog expanded: 291 + 1 = 292; 100 × 292 / 423 = 69.030732...% → 69.0%
Catalog member spans: 6,267 + 64 = 6,331
Catalog strict subtotal: 283 (the added adaptation is not a whole-declaration twin)

Primitives expanded: 150 + 1 = 151; 100 × 151 / 272 = 55.514705...% → 55.5%
Primitives member spans: 3,162 + 73 + 81 = 3,316

F2A: 306 = 150 + 94 + 10 + 3 + 20 + 2 + 1 strip adaptation + 26 remaining
```

The Primitives source declaration's 81-line span includes its docstring at 2800–2811 and code at 2812–2880. These revised expanded figures are lower bounds on the completed census, not an instruction to count every short textual overlap as a full member.

**Disposition.** Accept the two recorded public pairs, R4-2's correction of the previously double-described internal originals, and R4-3's measured spans. Carry the earlier source and debt closures. **Do not close R4-1 or retire epoch R1:** add the omitted strip-proof correspondence, reconcile the actual screen output and population, and qualify or adjudicate the remaining partial-reuse candidates. The gate requires zero blockers and majors, and two majors remain.
