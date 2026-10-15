**Retrofit epoch R1 — external audit findings**

**Verdict: gate remains open — 0 blockers, 2 majors, 2 minors, 8 notes.** The majors concern missing evidence for expressly required audit checks. I found no unauthorized change in the supplied patches and no mathematical counterexample. The recorded human decisions are credited; this report does not request renewed approval of already acknowledged debt or of E1.

Audit target: `c43f3a53`, relative to the recorded base `5588628cbbddea9546f616907364b608e15557fd`. Evidence: the supplied pack and its 20 attachments only. Bundle SHA-256, independently computed: `3d0a0f7415f22caa60ff21a9c11747eef2f786c4b0bfd8e5c36140c221c4200e`.

I accepted the commissioned premise that the changes are kernel-checked. I did not re-audit tactic correctness, access repository development history, or modify Lean sources. I parsed all 46 unified-diff hunks, checked their old/new line counts and inter-patch context consistency, independently enumerated the removals and additions, and tracked line positions through all seven agent commits and the maintainer's E1 diff.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| R1-1 | major | Audit pack §1/§3 · source reconstruction and `catalogPair_inverse` replacement | The packet does not supply the evidence needed for the requested full source reconstruction or literal comparison with the public Encoding lemma. | None of the three complete Lean source files is attached, at either the base or final revision. More specifically, the pack says the public `Turing.eq_pairEncode_of_pairDecode` is attached “in context via the patch,” but the E1 patch contains only the deleted private declaration and the replacement invocation. No attachment contains the public declaration. A successful rewrite at four call sites does not establish equality of the complete universally quantified statements. The change-boundary freeze check below succeeds, but full declaration-byte comparisons and blob rehashes cannot be independently reproduced from these excerpts. | Supply one complete pinned source state for each of the three files, so the patches reconstruct the other states, and the exact public Encoding declaration with its namespace/variable context. Then repeat the byte comparisons and the E1 statement comparison. No additional public-body permission is needed. |
| R1-2 | major | `workflow.md` §4 · epoch cumulative duplication ledger | The delivered ledger reports the change in duplication, but does not provide the required cumulative copied-material totals and fractions. | “New copies: none” is verified. The 5,713/7,636/8,904 line counts are total file sizes, not copied-material counts. The attached inventories give historical twin counts, selected approximate family sizes, and provenance descriptions; they do not give a reconciled final per-file copied-material numerator, denominator, and fraction. The 95 Loop and 150 Primitives twin maps are baseline inventories, and some originals have now been deleted. The complete twin sources/maps needed to independently verify the remaining provenance are absent. | Add a final per-file cumulative ledger, with named families/counterparts, exact counting convention, non-overlapping copied-material totals and fractions, and retained/deleted dispositions for the historical maps. Carry forward the recorded D-R2/D-R3 approvals and schedules. For any accumulated debt not covered by those decisions, the template's required disposition is **human acknowledgment required**, naming where and when it will be resolved. This finding does not demand fresh approval of already accepted families. |
| R1-3 | minor | Audit pack §2/§5 · deletion total | The epoch removes **83**, not 85, private declarations. | The patches remove 10 from Loop, 64 from Primitives including E1, and 9 from Hardness; they introduce no declarations. Thus `10 + 64 + 9 = 83`. The prose list also mentions `catalogPair_length` twice: within the two Encoding duplicates and again at its end. The line reduction of 1,639 is correct. | Record the pack erratum in the resolutions: **−1,639 lines, −83 privates**. Count `catalogPair_length` once. |
| R1-4 | minor | Audit pack §1 and plan §4d · public-freeze bookkeeping | The public inventory and post-E1 byte-identity wording need correction. | Loop has **8** publics including `stateWord`, not 9; the attached axiom log has exactly those eight names. Primitives has 18 and Hardness 5. Before E1 all 18 Primitives public bodies are unchanged; after E1 exactly one body contains the explicitly authorized identifier substitution. The plan's merged-RB2 row nevertheless says “18/18 publics byte-identical” without this qualification. | State the inventory as Loop 8 / Primitives 18 / Hardness 5. Distinguish unchanged signatures/statements/docstrings for all 31 from unchanged complete declaration text for 30, with the sole approved E1 body substitution. Preserve the historical pre-E1 agent attestation as such. |
| R1-5 | note — no findings | Three patch series · ownership, authorized boundaries, additions | The supplied changes obey the amended scope. | Every source path is one of the three owned files. All seven agent patches retain Codex authorship. All 83 removed declaration heads are private. Other edits are the named comments, the H4 consumer derivation, the RB2 private uses, the RB3 replacements including `clFreshTM`, and E1. No public head/signature is edited, no declaration is added, and the only import addition is `Build.Seam` in Hardness. | None. Full reconstruction remains subject to R1-1. |
| R1-6 | note — no findings | Deleted private families · pending consumers | No supplied pending-consumer obligation requires a removed original to survive. | The 76 initial dead-code targets match the three briefs exactly. The seven other removed lemmas are replaced at their current uses. Plan §4d explicitly orders deletion before 12.2c and requires the dead Catalog twins to be dropped later. The live `emCall*`, H3, Primitives F25a/F27a/F26, and Hardness relocation/reader/wipe families are retained. The §13 plan names `bufferedSecondCfg`/`a2_mapVirtual` as virtual-input precedents; neither is deleted here. | None for the supplied plan and inventories. Retain historical provenance in the later twin-disposition ledger; do not interpret an old twin map as a requirement to preserve dead originals. |
| R1-7 | note — no findings | `Build/Loop.lean` · H4 | The forwarding replacement is a strict simplification, and retaining `emLoopForwardCfg` is justified. | Two local lockstep lemmas, totaling 52 lines with their comments/separators, disappear. Their two-line caller becomes 19 lines citing `leftCfg_run` and `Turing.emit_run`, for a net reduction of 35. Padding and configuration commutation are local glue, not a new lockstep induction. `emLoopForwardCfg` is still in the retained consumer's statement and in the new commutation fact, so deleting it would require additional changes. | None. |
| R1-8 | note — no findings | `CookLevin/Hardness.lean` · `clFreshTM`, `clFresh_run` | The general-configuration seam citation preserves the displaced stream head. | The machine becomes exactly `seamCompTM clWipeTM.tm 2 clReadTM.tm (.inl none)`. The wipe endpoint is reused with only the control state changed; its stream cursor remains `pre.length`. The new proof passes `he`, `rfl`, and the strict pre-return exclusion `hf`, then invokes `clRead_run` at that cursor. There is no replacement by native initialization or a zero-head `Cfg.ofWords` seam. `clFresh_idle` and `clFresh_first` are unchanged. | None. |
| R1-9 | note — no findings | `CookLevin/Hardness.lean` · three strict swaps | All 13 reported replacement sites match the patches, including the final line numbers. | Two composition uses, one buffer-append use, and ten unary-length uses are present exactly as enumerated below. Composition retains the old time envelope through the output-length bound and monotonicity. The buffer equality is cited in the needed symmetric direction. Unary-length uses share the existing `clNative_fill true`. Task 2 reduces the file by 32 lines. | None. |
| R1-10 | note — no findings | RB2 report → `7224d118` → plan §4d · E1 approval trail | The governance trail is complete **as recorded in the packet**. | RB2 explicitly escalates the frozen public use and retains both it and the private lemma. The maintainer diff is labeled “needs your approval by merge.” The plan records PR #9 merged by the user and explicitly associates that merge with approval of `7224d118`. The E1 diff starts at RB2's final blob label `406229db` and changes exactly the escalated public line. | None for the recorded approval. The source-comparison gap is R1-1. This is verification of the attached decision trail, not independent authentication of a GitHub merge event. |
| R1-11 | note — no findings | Recorded errata · Encoding use, generated artifacts, Hardness count | The recorded corrections agree with the attached evidence at its stated level. | The public E1 use is visible in the patch and acknowledged in the plan. Hardness's inventory counts `361 + 186 + 4 + 1 + 1 = 553` privates and independently records `618 − 65 = 553`. The generated-artifact list has 1 in Nondeterminism, 1 in EXP, and 3 plus a 7-member family in SAT: 12 total, none assigned to Hardness. | None. The artifact-location claim is inventory evidence; those modules and their kernel inventory are not attached for a fresh enumeration. |
| R1-12 | note — no findings | Axiom logs and delivery scope | The attached axiom prints agree with the stated public inventory and contain no admission axiom. | There are 8 + 18 + 5 = 31 entries: `stateWord` is axiom-free; the remaining 30 list only `propext`, `Classical.choice`, and `Quot.sound`. No patch references or modifies an environment shim. The separate integration sweeps, lint runs, zip checksums, and merge placement are maintainer attestations, not independently replayed checks in this audit. | None under the commissioned kernel-checked premise. |

**Re-established patch boundaries and size ledger.**

These numbers are computed from the hunks. Starting absolute sizes/private totals are taken from the supplied baseline inventories; the deltas are independently counted.

| File | Lines before | Lines after | Line delta | Privates before | Privates after | Private delta |
|---|---:|---:|---:|---:|---:|---:|
| Loop | 5,713 | 5,515 | −198 | 214 | 204 | −10 |
| Primitives, including E1 | 7,636 | 6,374 | −1,262 | 318 | 254 | −64 |
| Hardness | 8,904 | 8,725 | −179 | 553 | 544 | −9 |
| Total | 22,253 | 20,614 | **−1,639** | 1,085 | 1,002 | **−83** |

The per-commit line arithmetic is:

- Loop: `5,713 + 2 − 165 = 5,550`; `5,550 + 19 − 54 = 5,515`.
- Primitives: `7,636 − 1,222 = 6,414`; `6,414 + 28 − 44 = 6,398`; E1 gives `6,398 + 1 − 25 = 6,374`.
- Hardness: `8,904 + 2 − 126 = 8,780`; `8,780 + 24 − 56 = 8,748`; `8,748 + 4 − 27 = 8,725`.
- Combined: `198 + 1,262 + 179 = 1,639`; `10 + 64 + 9 = 83`.

The recorded patch-index chains are internally consistent:

| File | Index chain printed in the patches |
|---|---|
| Loop | `c33e04c1 → 3e99b317 → dbb41eae` |
| Primitives | `3d969bdf → c1f48adb → 406229db → bf6244f1` |
| Hardness | `a27121c6 → 262e84fc → 830e1c3c → c63b4e7c` |

These are **not independently recomputed blob hashes**. I propagated the supplied text and line identities through the hunks without inventing missing text. The patches leave 5,458 base lines of Loop, 6,220 of Primitives, and 8,561 of Hardness unavailable. Thus they support an exhaustive classification of the supplied edits, but not the stronger claim that complete source files or complete public declaration bytes were recovered and rehashed.

For the freeze check, every removal block was classified against the binding briefs. Entire declaration removals start at the declarations' own docstrings and end before the next retained declaration. The sole partial-docstring removal adjacent to a deletion is the expressly authorized `clCount_width` sentence. The module/section comment hunks in Primitives do not edit `computesFunInTime_incFixed`, despite that theorem's name occurring in a diff hunk header. The following surviving declarations contain the substantive edits:

| File | Authorized retained material changed |
|---|---|
| Loop | One sentence in `loopHost_contracts`; the body of `emLoopHost_body_forward` |
| Primitives, agent patches | The three named comment regions; one use in `catalogPayload_length`; two use lines in `pairMap_computes` |
| Primitives, E1 | One use line in the public `computesFunInTime_stripLast` proof |
| Hardness | One sentence in `clCount_width`; `clCopy_write`; `clQueryCode_machine`; `clNative_image`; the ten enumerated unary-length uses; the body of `clFreshTM`; the proof body of `clFresh_run`; the sanctioned import |

Taking the pack's completeness assertion for the patch series as given, no other public text is changed. This independently supports the **relative freeze**: Loop 8/8 and Hardness 5/5 unchanged; Primitives 18/18 unchanged before E1, and 17/18 complete bodies unchanged after E1 with all 18 signatures, statements, and docstrings unchanged. The optional `splitSolve` stretch was not performed.

**Deletion accounting and future-consumer check.**

| Group | Independently enumerated removal count | Disposition |
|---|---:|---|
| Loop initial dead targets | 8 | Exactly `loop_silent_prefix`, `loopDebitTM`, `loopDebitCfg`, `loopBorrow_step`, `loopBorrow_run`, `loopBorrow_rewind`, `loopBorrow_correct`, `loopBody_capture` |
| Loop H4 proof pair | 2 | `emLoop_forward_apply`, `emLoop_forward_run`; replaced in the retained consumer |
| Primitives F24a/F24b/F24c/F24d/F24e/F24f | 59 | `6 + 13 + 18 + 11 + 9 + 2`; exact name set agrees with the brief |
| Primitives split orphans | 3 | `splitFind_none`, `splitCount_firstHalt`, `splitPrepare_first` |
| Primitives Encoding duplicates | 2 | `catalogPair_length` in the agent series; `catalogPair_inverse` in E1 |
| Hardness initial dead targets | 6 | Exactly `clRefClockTM`, `clRefClockCfg`, `clCount_first`, `clRefCountTM`, `clRefCount_first`, `clReadFields` |
| Hardness replaced lemmas | 3 | `clCompute_comp`, `clBuffer_append_bit`, `clA5_pt_unaryLength` |

The correct distinction is **76 already-dead declarations plus 7 eliminated by replacement**, not 83 declarations all dead in the baseline. Existing consumers of the latter seven are redirected as part of the changes.

The pending-program check does not rely on private visibility alone: a future harvest could still need a private's source. Here the supplied plans explicitly request these deletions, retain the needed live templates, and schedule removal of the corresponding dead Catalog copies. In particular, the old `emitterBank*` relocation target is superseded and deliberately deleted; its historical mention is not an instruction to preserve it for §13. H3's agreement-transfer consumer and the `emCall*` clean-call templates survive. Primitives' compare, erase, relocation, and split-controller material scheduled for later work survives. Hardness's live parallel bank and its noncanonical wipe/read/relocation infrastructure survive.

The full §13 design document and complete counterpart sources are not among these 20 attachments. I therefore do not extend this conclusion to unprovided consumer specifications or claim to have independently recomputed Catalog's liveness graph.

**Replacement reasoning.**

For H4, the added tape is inactive under `leftAction 1 id`. `leftCfg_run` supplies the entire padded trajectory, including its unchanged extra tape and head. Mapping the source state by the identity preserves the source liveness premise at every strict-prefix time. The local `Cfg.ext` fact commutes padding with `emitCfg`, and the transition agreement commutes padding with `emitAction`. Applying the public `emit_run` then gives exactly the retained consumer's endpoint, including the final action's optional emission. No stronger liveness requirement at the final time is introduced. At time zero both sides remain the same padded, prefix-adjusted initial configuration. The actual global lockstep proof and induction have been removed.

For `clFresh_run`, the wipe retains the stream word `pre ++ pairEncode w tail`, its cursor `pre.length`, and native input position `p`, while clearing the target and returning its target head to zero. The seam's single dispatch changes control only. The second phase therefore starts at the exact empty-target `clReadCfg` used by `clRead_run`, even when `pre` is nonempty. The returned stream cursor is `pre.length + 2 * w.length + 2`, with the new target word `w` and target head zero. The duration remains `a + 1 + (3 * w.length + 3)`, under the existing bound `2 * old.length + 3 * w.length + 6`. Empty `old`, empty `w`, and nonzero stream cursors require no new hypothesis. The general configuration contract is essential to this simplification. Task 3 removes 24 lines from the construction/proof and adds the one import, for a net reduction of 23.

The composition swaps remove a 22-line helper and add only output-length/monotonicity glue at its two callers. The useful inequality is the existing consequence of the first completed computation: `y.length ≤ a`, where `a` is that computation's time allowance. It is used to retain the old `2 * a + b + 2` allowance after citing the public composition row. `clNative_image` already contains the intermediate-length estimate for its polynomial envelope. No output-independent bound for the second machine is asserted: its contract is still used on the first machine's actual output. The exact public composition declaration is not reproduced in this packet, so this is an audit of the supplied replacement and its kernel-checked use, not an independent restatement of that library declaration.

**All 13 Hardness use sites, independently located after the complete RB3 series:**

| Removed helper | Retained caller | Final line |
|---|---|---:|
| `clBuffer_append_bit` | `clCopy_write` | 1,636 |
| `clCompute_comp` | `clQueryCode_machine` | 4,984 |
| `clCompute_comp` | `clNative_image` | 5,145 |
| `clA5_pt_unaryLength` | `clA5Drop_native` | 6,833 |
| `clA5_pt_unaryLength` | `clA5Field_native` | 6,901 |
| `clA5_pt_unaryLength` | `clA5StoredRound_native`, header field | 7,012 |
| `clA5_pt_unaryLength` | `clA5StoredRound_native`, header tail | 7,013 |
| `clA5_pt_unaryLength` | `clA5Next_native` | 7,029 |
| `clA5_pt_unaryLength` | `clA5Sizes_native`, header field | 7,570 |
| `clA5_pt_unaryLength` | `clA5Sizes_native`, header tail | 7,571 |
| `clA5_pt_unaryLength` | `clA5Cursor_native` | 7,933 |
| `clA5_pt_unaryLength` | `clA5Indices_native` | 7,955 |
| `clA5_pt_unaryLength` | `clA5Fragment_native` | 8,032 |

**E1 and the residual ledger.**

The deleted private's complete proposition is supplied:

```lean
private lemma catalogPair_inverse (x : List Bool) :
    ∀ a v, pairDecode x = some (a, v) → x = pairEncode a v
```

Its four previous code uses are accounted for: one in `catalogPayload_length`, two in `pairMap_computes`, and the last in the public `computesFunInTime_stripLast`. RB2 replaces the first three and leaves the fourth frozen. E1 then replaces the fourth and removes the 24-line declaration block. This is the declared exception, not an unreported agent violation. What remains missing is the other declaration required for the exact statement comparison.

The existing acknowledgment is substantive: D-R2 explicitly commissions 12.2c immediately after the retrofit, names the 150/95 historical twin families and Wrappers copies, and calls for one implementation with time and space contracts. D-R3 commissions the agreement-transfer machinery for Loop H3. These decisions should be carried into the resolutions; there is no reason to ask the human to approve those same families again.

Nevertheless, a current cumulative ledger cannot simply call the old maps “untouched.” All 95 original Loop core declarations had Catalog counterparts; 8 originals have now been deleted, leaving **87 original-side members** of that historical correspondence. Catalog's copies were not edited. The three deleted Primitives split orphans likewise had entries in the baseline twin families; other Encoding-copy dispositions also need to be reconciled against the actual map. The rewritten Primitives comment continues to disclose an additional live cross-file relocation harvest from Loop's `emCall` family. None of these facts is evidence of a new copy; all are reasons to supply the required final accounting rather than substitute a net-negative line delta for it.

Glossary: `a` and `b` are the first and second computation time allowances in the composition discussion; `y` is the intermediate word. In the seam discussion, `pre` is the stream prefix, `old` the previous target word, `w` the field being read, `tail` the following stream suffix, `p` the native input-head position, and `a` the wipe duration. These are the corresponding source declarations' variables.
