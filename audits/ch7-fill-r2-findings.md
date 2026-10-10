# Chapter 7 fill-gate audit — round 2

**Result: 0 blockers, 2 majors, 2 minors, 2 notes. The gate remains open.** The two majors concern duplication governance, not a refutation of the kernel-checked statements. Questions 1–6 from round 1 transfer unchanged.

Audited snapshot: `Shilun-Allan-Li/tcslib`, branch `complexity/arora-barak-ch3-4`, commit `4502c30fd24b054834b66b4621f06b91db545ee6`. Supplied bundle SHA-256: `4c8d52b6e01e37c49e5883a5d9eb808b8271026d42b9dbf8c85e2b667ac46447`.

I used the bundle, verified its eight Lean files against the pinned Git tree, and fetched the relevant existing run infrastructure at that same commit. The comparison with the round-1 tree used `0c22ae33a2321ea027261efa3608ad952b3cd9a5`. Proof text was examined for duplication, not for tactic correctness. No Lean build was run.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| R2-1 | major | `Build/EmitIterEmbed.lean` · `step_output_prefix`, `runFrom_output_prefix`, `runFrom_output_extends`, `runFrom_of_halted`, `state_isSome_of_runFrom` | The claim that no pre-existing proved material is reproduced is false. Five run-infrastructure facts are re-proved, putting this file at **at least 5/18 = 27.8%**. | Exact statement correspondences or immediate specializations of existing results are listed below. Two counterparts are private in `Build/Loop`; the new proofs rederive them instead of sharing them. Adding these source files to the screen still produces the same 24 hits: these are genuine coverage misses. | **Human acknowledgment required.** Record this proved-material family and its threshold crossing, and explicitly accept its owner and scheduled resolution. The existing design-parallel watch item does not record this census. Even if the existing 12.2c scope is interpreted to cover the family, a further file crossing one fifth is expressly a major under the amended rule. |
| R2-2 | major | `audits/duplication-ledger.md`, CH7-D1; `PolyTimeBlockTests.lean`, `PolyTimeBlockMajority.lean` | The six disclosed copy-side members are real, but their accounting is neither the standing source-inclusive census nor the full extent of the family. Applying the standing rule crosses one fifth in a further file. | The six disclosed pairs alone have **7 distinct members in Tests: 7/25 = 28%**, rather than 2/25. Four further cross-file proof adaptations are exhibited below; they raise the confirmed lower bounds to **10/25 in Tests and 8/14 in Majority**. | **Human acknowledgment required** for the newly established Tests threshold crossing. Retain the already accepted 12.2c resolution; reconcile the source/copy union and missing members under one stated convention. The original acknowledgment is valid for the disclosed debt, but the template explicitly makes this threshold-changing correction major. |
| R2-3 | minor | Duplication-screen method description; ledger's EmitIter watch item | Some descriptions overstate the screen, and the body-module declaration count is stale. | `toks` collapses identifiers to one `ID`, without checking a consistent renaming; `most_common(1)` prints only the strongest partner per declaration and mode. It compares whole declaration text, including definitions against proofs. The script itself counts `EmitIterBody` as **20 declarations, 1 public and 19 private**, whereas the watch item says 1 public and 17 private. | Describe the actual heuristic and its coverage; correct the body inventory. Treat the reported overlaps as candidates requiring classification, not an exhaustive correspondence census. |
| R2-4 | minor | `audits/ch7-fill-pack.md` · EmitIterEmbed scope row | Round-1 finding 2 is corrected in the module summary but remains in the attached pack's inventory. | That row still lists `control_step` and `control_step'` among `EmitIterEmbed`'s public results. Both remain private declarations of `EmitIterBody`. The attached sweep does not edit the pack. | Correct the inventory as well. The requested module-comment corrections are accurate; no API change is needed for this finding. |
| R2-5 | note | `Build/EmitIterEmbed.lean` versus `Build/Embed.lean` | The layers have overlapping simulation purposes but materially different contracts. Neither supplied API simply states everything the other does. | The factual comparison below covers state maps, frame contents, tape selection, output, first return, and avoidance. | Use these facts to scope the already scheduled 12.2c work. No merge proposal is made here. |
| R2-6 | note | Transfer attestation and round-1 comment sweep | The formal transfer and the three requested comment changes check out. The malformed-input paragraph is accurate, including nested pairs. | Six Git blobs are identical across the two snapshots. The other three files agree after stripping comments and whitespace. Reversing the sweep reproduces its three advertised preimage blob IDs. The malformed-input reductions are given below. | Carry questions 1–6 forward. Preserve the corrected comments; finish the inventory correction in R2-4. |

## 1. Duplication and the pre-screen

### Mechanical reproduction and limits

The pinned recursive Git tree contains **562 `TCSlib/**/*.lean` files**. The supplied bundle contains eight of them. Running the **unmodified** supplied script on those eight reproduces every line of the recorded result except the haystack-size label: **112 declarations, 3 exact-mode hits, 21 renamed-mode hits**, with identical partners, percentages, and shingle counts.

I then added the pinned `Configuration`, `Deterministic`, `Finite`, `Simulation`, `Build/Loop`, and `Build/Primitives` sources and reran it on fourteen files. The 24 reported hits remained identical. Thus the positive results are reproducible, but the absence of a reported hit does not exclude re-proved material. I did not independently replay the entire 562-file corpus; the supplied full-tree run remains evidence for that execution, not a proof of semantic nonduplication.

The surface total is

`18 EmitIterEmbed + 20 EmitIterBody + 32 BlockLoop + 25 Tests + 14 Majority + 3 PClosure headlines = 112`.

The “renamed” mode preserves keywords and punctuation but maps most ASCII-leading identifiers to the same token. It does not preserve which occurrences refer to the same identifier, and it does not abstract all Unicode identifiers. Its shingles are sets, not occurrence counts. The script reports a best partner, not every qualifying pair. These qualifications explain both false positives and omissions; they do not invalidate the reproduced output.

### Existing run facts reproduced in EmitIterEmbed

All source locations below are at `4502c30f`; line numbers refer to the actual Lean files, excluding bundle fences.

| EmitIterEmbed declaration | Existing result | Correspondence |
|---|---|---|
| `step_output_prefix`, lines 114–124 | `Build/Loop.lean`, private `FinTM.emLoop_step_prefix`, lines 4653–4667 | Identical configuration equality, after changing binder names and argument order: stepping with an existing output prefix equals prefixing the resulting configuration's output. |
| `runFrom_output_prefix`, lines 127–135 | `Build/Loop.lean`, private `FinTM.emLoop_run_prefix`, lines 4672–4680 | Identical run equality. The new proof inducts from the front of the run; the old proof inducts on the final step. That restructuring evades contiguous matching. |
| `runFrom_output_extends`, lines 138–155 | `Finite.lean`, `MultiTapeTM.output_prefix`, lines 105–117 | Specialize the existing theorem to times zero and `t`. A list-prefix witness is exactly an appended suffix, up to reversing the equality. The new declaration repeats the append-only induction. |
| `runFrom_of_halted`, lines 160–166 | `Deterministic.lean`, `MultiTapeTM.runFrom_of_halt`, lines 225–227 | The same statement specialized to Boolean symbols, with explicit/implicit arguments rearranged. The new declaration gives another induction instead of citing the existing theorem. |
| `state_isSome_of_runFrom`, lines 169–181 | `Build/Loop.lean`, private `FinTM.loop_live_prefix`, lines 183–192 | A live endpoint implies every state at an earlier or equal time is live. For `Option` states, “not `none`” is equivalent to “equals `some q` for some `q`.” The new proof repeats the same absorbing-halt contradiction. |

These five target declarations occupy **58 code lines** before docstrings. The three relevant private Loop declarations are also unchanged from the round-1 fork tree; they are not newly introduced by the merged-tree adaptation. The `Finite` blob is identical across those snapshots.

The public visibility of the new facts does not remove the debt. Exporting shared infrastructure can be useful, but independently re-proving an already established routine fact still falls within the pack's requested non-mechanical check. This finding concerns these five specific correspondences, not the proposition that every short adapter or every embedding construction is a copy.

### The acknowledged block-loop family

All six disclosed copy-side entries are confirmed. Their four Majority code spans are **15 + 16 + 46 + 8 = 85 lines**, so the displayed 4/14 copy-side calculation is correct. The two Tests entries occupy **16 + 30 = 46 code lines**; the screen table's 21-line entry for `xorStep_orbit_done` is not its 16-line declaration span.

However, the ledger's stated membership rule counts **either side** of a qualifying cross-file correspondence, once per file. The six disclosed pairs already give this source-inclusive union:

| File | Members contributed by the six disclosed pairs | Total |
|---|---|---:|
| `PolyTimeBlockMajority` | `length_majStep_iterate`, `majStep_orbit_done`, `length_majStep_le`, `polyTimeComputable_majInit` | **4/14** |
| `PolyTimeBlockTests` | `length_xorStep_iterate`, `anyStep_orbit_done`, `length_xorStep_le`, `polyTimeComputable_anyInit`, `xorStep_orbit_done`, `xorLoop_output`, `anyLoop_output` | **7/25** |

The later-copy-only convention is explicitly stated in the Chapter-7 pre-screen, but it is different from the standing ledger convention. Both numbers can be reported under distinct labels; **2/25 cannot stand in for the cumulative source-inclusive Tests total**. This is why R2-2 invokes the amended rule's further-file threshold exception, rather than treating every accounting correction as major.

The screen also misses substantial cross-file adaptations within the same loop family. For reproducible witnesses, I stripped comments and whitespace from proof bodies, consistently replaced the corresponding `anyStep`/`majStep`, `anyEmit`/`majEmit`, `anyInit`/`majInit`, and associated helper names by shared names, and found disjoint matching blocks of at least 25 characters. These are lower bounds on reproduced source text, not the published shingle scores:

| Tests source → Majority counterpart | Shared source-proof characters | Reproduced argument |
|---|---:|---|
| `polyTimeComputable_anyStep` → `polyTimeComputable_majStep` | 1056/1157 = **91.3%** | The same guard, countdown, payload, and conditional-composition assembly, with additional vote operations. |
| `polyTimeComputable_anyEmit` → `polyTimeComputable_majEmit` | 379/406 = **93.3%** | The same two guarded emission branches, with a vote-comparison computation inserted. |
| `anyStep_orbit` → `majStep_orbit` | 749/926 = **80.9%** | The countdown/slicing induction and block advance recur; the vote-counter arithmetic is additional material. |
| `anyLoop_output` → `majLoop_output` | 795/853 = **93.2%** | The same budget domination and before/at/after-exhaustion argument using `flatMap_range_eq_single`; majority adds the count comparison. |

These four additional target members produce **at least 8/14 = 57.1% in Majority**. Three of their sources are new to the seven-member Tests union (`anyLoop_output` was already included), yielding **at least 10/25 = 40% in Tests**. Even excluding the two disclosed in-file copy-side entries, the eight cross-file source members exhibited here alone give **8/25 = 32%** in Tests. Thus the crossing does not depend on how the in-file exception is applied.

Two further length correspondences also merit recording. `Tests.length_anyStep_le` contributes 953/1370 = **69.6%** of its normalized proof to `Majority.length_majStep_le`, adding another source-side member. `Tests.length_anyStep_iterate` has exactly the same proof body as `BlockLoop.length_xorPairStep_iterate` after substituting `(anyStep V a k) → xorPairStep` and `length_anyStep_le V a k → length_xorPairStep_le`; it adds another Tests member and one BlockLoop member. The confirmed totals therefore reach **at least 12/25 in Tests, 8/14 in Majority, and 1/32 in BlockLoop**. These are lower bounds, not an assertion of an exhaustive replacement census. The threshold-changing discrepancy already follows from the earlier, smaller inventories; the additional evidence belongs in the same reconciliation.

The named generic-lemma resolution remains plausible: the repeated guard, countdown, orbit, and single-emission reasoning can be shared while retaining separate OR/XOR/vote computations. I found no reason here to declare that resolution impossible.

### Class B and the borderline cases

| Candidate | Verdict |
|---|---|
| `polyTimeComputable_take1` / `polyTimeComputable_tail` | Accept the mirror classification: distinct take/drop operations, proved by the corresponding existing primitives. |
| `polyTimeComputable_sliceTakeAt` / `polyTimeComputable_sliceDropAt` | Accept the mirror classification: the same scheduling interface applied to the complementary take/drop operations. |
| `embed_ofWords_left` / `embed_ofWords_right` | Accept as the two symmetric module instances, with their respective positivity premises and state constructors. Both cite `embedCfg_ofWords`. |
| `length_pairSndD_le` / `PolyTimePairing.length_pairFstD_le` | Accept the projection-dual classification. The 19-shingle match is a short decoder case split for different projections. |
| `length_xorPairStep_le` / `length_sliceDropAt_le` | Record an **in-file near-duplicate**, not an unreported cross-file family. Their proof bodies are exactly equal after the explicit substitutions `sliceDropAt → xorPairStep`, `z → s`, `p → a`, `u → b`; their full declarations differ in parameters and operation. Under the ledger's explicit convention for in-file near-duplicates, record it without adding a census member. It is more precise to disclose this than to describe it merely as a coincidental proof shape. |
| `majStep` / `polyTimeComputable_majStep` | Exclude this definition-versus-proof match. The proof restates the definition's case expression to establish its complexity; this pair is not two copies of proved material. The separate cross-file proof adaptation listed above is a different comparison. |

## 2. EmitIter versus Build/Embed: contract facts

| Aspect | `EmitIterEmbed` | `Build/Embed` |
|---|---|---|
| State transport | `embedCfg` maps `SS → B`; **no injectivity hypothesis** is imposed despite the parameter name `inject`. `embed_step` can start at an arbitrary host state `b` with the required transition. `padAction` itself accepts an arbitrary function on optional states. | The closed transformers preserve the state type. The returning transformers use the specific tags `Sum.inl` and `Sum.inr ()`. These APIs do not quantify over an arbitrary host state map or arbitrary matching host transition table. |
| Tape placement | The first `m` of `k` tapes, using `Fin.castLE` and `m ≤ k`. | Any genuine injection `ι : Fin m ↪ Fin k`, with source tape coordinates preserved. This is whole-tape relocation, not multiple virtual tapes packed onto one physical tape. |
| Unselected tapes | `embedCfg` initializes them blank, heads zero. `padAction` leaves them untouched, but the supplied run theorem starts from that blank-padding configuration. | Explicit arbitrary frame tapes and head positions are carried through the run; frame theorems state their preservation. In the silent flavor, the designated capture tape has its specified buffer contents instead. |
| Output | Actions forward the source emission. Configuration transport preserves source output. Separate public theorems state output-prefix commutation and append-only extension. | Forwarding transport has output `pre ++ c.output`. Silent transport captures that word on `cap`, keeps physical output `out₀`, and requires `cap` outside the selected bank in its public run contracts. Both execute a final halting transition's emission. |
| Simulation premise | `embed_run` compares an arbitrary host and module, requiring matching transitions away from `ex` and live, non-`ex` source states at every `j < t`. The endpoint may halt or reach `ex`. | Closed transformers supply their own transition tables; their lockstep theorems hold for all durations, including halted tails, with no avoidance or liveness guard. |
| Avoidance / return | `SafeRun` means endpoint equality plus avoidance for **all `j < t`**, including zero. It has zero, prepend, and concatenation laws. It requires neither a live endpoint nor an avoided endpoint. A positive anchor-to-anchor round is therefore not a `SafeRun` avoiding its own starting anchor. | Returning contracts assume a live start, liveness before `T`, and halt at `T`; they conclude live return at time `T`, with no earlier return-anchor visit. They execute through the source halt. The public contracts exclude an initially halted zero-time handover. No general `SafeRun` composition API is stated here. |
| Space | No explicit visited-set or per-tape-space contracts in this module. | Selected-tape visited-set equality, stationary frame sets, capture-space bound, and returning/closed visited-set comparisons are exported. |

In particular, source avoidance alone does not imply avoidance of `inject ex` in an arbitrary host: distinct source states may share their image. The actual body uses disjoint constructors and proves the needed anchor exclusion. This qualifies the word “injection” without reopening the already accepted forward-simulation theorem.

The supplied `Embed.lean` has filled proofs, notwithstanding stale “statement skeleton / all sorried” module prose. The comparison above follows its declarations, not that historical status description.

## 3. Transfer and comment-sweep verification

All eight bundled Lean files have Git blob hashes equal to their entries in the pinned merged tree. Comparing the nine round-1 files with `0c22ae33` confirms the claimed six byte-identical blobs. For `EmitIterEmbed`, `PolyTimeBlockLoop`, and `PClosure`, I fetched the old contents and independently confirmed equality after removing nested block comments, line comments, and whitespace. The old SHA-256 prefixes match the attestation: `de94b02751582f84`, `5654f6f1b1b12025`, and `5481969b35302efd`.

The attached diff reverses cleanly against the bundled final files. Its reconstructed preimage Git blobs begin `424ec64c` (EmitIterEmbed), `611d5e11` (BlockLoop), and `0370605d` (PClosure), exactly as its index lines specify. Every changed character lies in a block comment. The additional fork-to-pre-sweep PClosure differences are precisely the two default-projection docstring corrections described by the transfer attestation.

- The XOR bullet correctly credits the emit-iteration construction used by `polyTimeComputable_xorD`.
- The EmitIterEmbed summary correctly removes the two nonexistent public exports and identifies the private body helpers. Only the older pack inventory remains stale (R2-4).
- The new PClosure paragraph accurately describes default decoding and re-encoded queries. It does not impose malformed-input rejection.

For the last point, the reductions are explicit:

1. If the outer pair decoding fails, both default components are `[]`. The first-component length is zero, so the scheduled query count is `a' * (0 + 1)^k' = a'`. Every ordinary block is empty.
2. In the nested headline, outer failure also makes the inner components and the mask empty. If the outer pair is valid but its inner word is malformed, the two inner components are empty while the outer mask is retained. In either case every queried block is empty, and `List.zipWith xor mask [] = []`.
3. Consequently, in each malformed case just described, every query is exactly `pairEncode [] []`. Each of the three headline languages accepts exactly when **`0 < a'` and `pairEncode [] [] ∈ V`**: OR needs one query, and strict majority of a constant answer accepts precisely under the same condition. With zero queries all three reject. The retained outer mask has no effect after XOR truncation against an empty block.

This establishes the advertised totalization, including the nested case, directly from the displayed statements and `blockAt`. No newly added comment misstates that behavior.

The seven-module recheck log records seven zero exits. The carried merged sweep records 23 successful checks and the disclosed concentration admission; the axiom log has 36 entries, with `sorryAx` only for that disclosed result. These execution logs, and the reported lint result, were not independently regenerated. They do not resolve the two duplication-governance majors above.
