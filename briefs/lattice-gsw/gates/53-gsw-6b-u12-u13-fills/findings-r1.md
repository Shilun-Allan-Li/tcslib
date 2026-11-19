**Gate 53 · GSW phase 6b fills U12/U13 · round 1 · PR #392: CLEAR.**

| Item | Audited value |
|---|---|
| PR head | `4b2ede271e1af88ad2eee207dafd9b674f19a306` |
| Records pin | `761852890a3ba7b0ea7852d179266ca85c366b37` |
| Frozen statements, B6 | `bff0567b6c4b6b724c8fd20ff3ef92258eb3fc9d` |
| PR `TCSlib` tree | `745bf4b494b6581a5666ef9ca0a6e735a68ddcef` |
| Computed review ZIP SHA-256 | `5a220db3c56024d4de5f760e75aeb5b741d2b670c2398a2a3e273dbb69b97202` |
| Duplication sources | Mathlib `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`; Batteries `39260e31b7b3f7f05643da95242463b462dc05f1` |

All seven requested commits exist. The fetched landing branch equals the audited head. This was a reading audit: no Lean, Lake, build, olean download or Mathlib cache operation was performed. Repository content was read only; nothing was pushed, commented on or submitted.

| # | Severity | File · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|
| **G53-01** | **minor · evidence** | Review ZIP, `probe-src/DupProbe.lean:21`, **D3**; U13 `final-r1/phase2.md`, P2-6 | D3 omits `[NeZero q]`. Its universally quantified statement is false, so its failed `exact?` search does not establish the claimed absence of a lemma for G6's actual domain. | At modulus zero, `ZMod 0` is the integers and `.val` is absolute value. With two true weights and residues `1, -1`, the left side is `abs(1 + (-1)) = 0`; the right side is `(abs(1) + abs(-1)) % 0 = 2`. The pinned Mathlib definitions establish this directly. G6 has a nonzero modulus and uses `ZMod.natCast_zmod_val` correctly. Independent source searches below support the duplication conclusion without D3. | Publish a corrected D3 with `[NeZero q]` and update the review's interpretation of that probe. No PR source change is needed. |

**A. Proof correctness.** All nine targets and the private glue establish their frozen statements by reading; the source-bound replay supports this assessment.

| Target | Assessment |
|---|---|
| G1 `Encrypts.select` | In each bit case, `mul_bit` gives noise `P.columns * β + βV` on the product whose left message is one; `mul` gives noise `P.columns * β` when the left message is zero. Addition gives exactly `βV + 2 * (P.columns * β)` and message `(1-b)*u+b*v`. Both cases are covered. |
| Private `encrypts_select_ite` | Cites G1 and cases on the Boolean selector. The cast and branch order agree with its formula docstring. It holds for arbitrary natural messages, as G2 needs. |
| G2 `encrypts_homEvalPBP` | The relation carries the stated noise at every coordinate. The initial `Pi.single` states use gadget/zero encryptions. The two permutation readers justify both pull steps; the glue advances the noise by `2 * (P.columns * β)`. `evalWith_rel` has the correct selectors, inputs and initial states. `evalWith_single` and the final two-case indicator identity finish the stated result. |
| G3 `encrypts_homEvalFormula` | Applies G2 to the stated Barrington program and accepting coordinate. `barrington_yield_zero`, the reader-based computation that `sigma1` moves zero, and the two Boolean cases give the message. `barrington_length_le` gives the frozen noise bound. |
| G5 `vecMul_secretVector_eq_sum` | Gadget reconstruction gives the lifted key vector; `dotProduct_mulVec`, the constants reader and commutativity give the sum. The closing `rfl` reads Mathlib's dot product. |
| G6 `decryptFormula_eval` | Uses the required decryption reader. The cast/sum calculation gives the representative modulo the nonzero modulus. The endpoint readers and `modulus_ge_two` justify both interval inequalities. F9 and O2 then give identical Boolean tests. |
| G7 `nandFormula_eval` | The NAND, negation and conjunction readers followed by G6 twice give exactly the two decryptions' NAND. |
| G8 `depth_nandFormula_le` | F10 bounds both operands; the conjunction bound and depth-preserving negation give `decDepth P + 1`. |
| G8 `maxFanin_nandFormula_le` | F10 bounds both operands by two; the conjunction and negation bounds preserve that bound. |
| G8 `decDepth_le` | `clog_le_iff_le_pow` gives `Nat.clog 2 P.lwe.modulus ≤ P.width`; monotonicity weakens F10 to the stated right side. No linear width term enters. |

The stored axiom evidence covers **13 Branching constants and 23 DecryptFormula constants**, including the private glue and compiler auxiliaries. All nine targets have exactly the standard three axioms; owner constants have no `sorryAx` or other nonstandard axiom. The false `sorry` control is flagged. Probe-source and raw-log hashes match the execution records.

| Question | Assessment and evidence |
|---|---|
| **B · Frozen statements** | **PASS.** All nine headers and statement-prose regions are byte-identical to B6. Independently restoring the nine bodies, three U12 sketches, two admission sentences and removing the one private helper reproduces both B6 files byte for byte. Definitions, readers, instance, imports, options and surrounding text are unchanged. The updated sketches and module sentences are accurate; all six U13 sketches remain accurate unchanged. The helper precedes its sole use and has no attribute. |
| **C · Scope/integrity** | **PASS.** Exactly the two owned files change, +157/−20. Each commit changes its delivered owned path. All three stable patch IDs match: `9748012790904bff1cd700a8a03a8f9cdc8a4b23`, `6bb343bddfbcd801ce646b7f01c12370ba8fdede`, `583a7750c6428c22ec78aeafdf5bd5f008e9b40b`. Delivered sources and evidence's frozen head/base files equal the corresponding Git blobs. All three packed diffs match independently generated diffs using the staging serialization, `--abbrev=9`. |
| **D · Rulings** | **PASS.** Q-U12-1/Q-U13-1 A resolves the records omission. Q-6B-F2 reserved `decDepth_le` for this fill; the unchanged statement is now proved from F10. Q-U12-3 A is respected: the private general lemma is neither promoted nor copied. G6 cites `decrypt_eq_decode_dotProduct`, satisfying Q-C1. No worker choice needs an unrecorded Q-6BF answer. |
| **E · Duplication** | **PASS, with G53-01's probe qualification.** Name and statement-shape searches found no additional undisclosed or unaccepted re-proof. D1 composes single-coordinate and decision lemmas; D2 composes the two published permutation readers. D3's actual-domain calculation composes cast/sum lemmas; D4's endpoint inequalities have no matching public lemma. The glue cites G1; `decDepth_le` cites F10. Every applicable must-reuse item is used. The reviews correctly explain why `mul_eq`, `encrypts_iff`, the family permutation reader, `isFiveCycle_iff`, `secretVector_eq` and `vecMul_secretVector_augmented` are unnecessary here. |
| **F · Policy/form** | **PASS.** G2's 42-line and G6's 20-line bodies have accurate sketches and step comments; the other sketches also agree. The private helper has its cast-correct formula and glue note. Source tags/anchors are unchanged. Files have 268/264 lines, maximum widths 97/98, and zero over-width lines, tabs, trailing whitespace or micro signs. Stored lint FAIL/WARN sets are unchanged; owner style logs report zero findings. |
| **G · Rule 10** | **PASS.** Every rewrite/simplification argument and definitional closing step was read. Foreign TCSlib content is consumed through readers; the computational steps reduce permitted core/Mathlib definitions. Independently checked closure/request sets contain exactly 200/380 seal candidates in both variants. Removing instrumentation restores the exact head sources. All four sealed executions pass with complete install/EOF verification; the 10/6 term exclusions are reducible notation. Both liveness pairs per owner fail only at their sealed negatives; positives and open copies pass. The explicit scan's 63 occurrences resolve to zero TCSlib definitions. No unjustified exclusion was found. |
| **H · Evidence binding** | **PASS.** Independently hashing B6's tree entries with the two delivered blobs reconstructs scratch root tree `fb6884d14882417682957ee056aab4bf6376652c`; its `TCSlib` tree equals the PR's. All 34 stack/alone build source and raw-log hashes match the appropriate pinned sources; records show 12/12 and 11/11 + 11/11 rc 0. The independently computed downstream closure has exactly 12 modules. Four full-order checks each contain 1,456 distinct OK rows. Admission names equal the base minus the respective targets: 33/14, 39/15 and 36/15. Snapshot rehash reports agree. Necessary evidence binds; D3 is qualified under G53-01. |
| **I · Disclosure/review** | The new issue is G53-01. The supplied slips are disclosed, including the review's directory/file miscount, the unrecorded Q-U12-2 answer and the signing/date details; they introduce no additional PR defect. The prior findings are graded below. Rule 15's scoped check passes: no target gains a hypothesis, and the helper assumes correctness/noise predicates rather than efficiency claims. |

**Integrity counts.** Pack: **7/7**. Review ZIP: **230/230** manifested files, plus its unlisted manifest; 272 ZIP entries comprise 231 files and 41 directories. U12 delivery/evidence manifests: **409/409 and 403/403**. U13: **172/172 and 167/167**. Path sets are complete and duplicate-free. Both filed review ZIP copies have the computed hash above. The source-head record's cited record/review hashes also match.

| Prior finding | Auditor grade/disposition |
|---|---|
| U12-F01 | **Agree: historical minor, records side; resolved for this PR** by Q-U12-1/Q-U13-1 A. No new finding against #392. |
| U12-F02 | **Agree: note.** Using `mul_bit` twice overcharges the state noise; the delivered mixed route reaches the frozen bound. |
| U12-F03 | **Agree: note.** Reader-based kernel computation is permitted; Q-U12-3 A keeps the general lemma private. |
| U12-F04 | **Agree: note.** Disclosed worker-host housekeeping has no in-scope source effect. |
| U13-F01 | **Agree: historical minor, records side; resolved for this PR**, shared with U12-F01. |
| U13-F02 | **Agree: note.** F2 is discharged as planned by the cited F10 specialization. |
| U13-F03 | **Agree: note.** The process-cap slip is disclosed; the independent maintainer replay supplies the relevant source-bound execution evidence. |

**Independent searches.** Exact commands, patterns and matches are in `searches.log`; `searches.py` also performs comment-stripped, multiline declaration-header searches. Counts below are matching source lines for S01–S13 and matching declaration headers for S14–S17, at the pins above. TCSlib's scope is `TCSlib`; the upstream scopes are their Lean source files.

| Search | Purpose | TCSlib | Mathlib | Batteries |
|---|---|---:|---:|---:|
| S01 | New helper name | 0 | 0 | 0 |
| S02 | Selector/encryption predicates | 7 | 0 | 0 |
| S03 | D1 single/decision/toNat names | 4 | 0 | 0 |
| S04 | D1 single/indicator/conditional relatives | 4 | 28 | 0 |
| S05 | D2 instruction/permutation shapes | 4 | 0 | 0 |
| S06 | D3 representative-sum lemma names | 0 | 2 | 0 |
| S07 | D3 value/modulo/Boolean-weight shapes | 42 | 7 | 3 |
| S08 | D4 decoding endpoints | 23 | 0 | 0 |
| S09 | G3 moved-zero facts/private relative | 6 | 0 | 0 |
| S10 | G8 depth-bound relatives | 18 | 0 | 0 |
| S11 | G1/G2 nearby public noise APIs | 8 | 0 | 0 |
| S12 | Public permutation APIs | 9 | 0 | 0 |
| S13 | G5/G6 algebraic relatives | 4 | 0 | 0 |
| S14 | D1 single/decision header shape | 1 | 0 | 0 |
| S15 | D3 finite-sum/value header shape | 1 | 3 | 0 |
| S16 | D4 endpoint-comparison header shape | 1 | 0 | 0 |
| S17 | D2 instruction-membership header shape | 1 | 0 | 0 |

The two S06 Mathlib hits concern adic completion. S14 finds the frozen G2 target itself. S15 finds `dotPoly_encodeVector` and three unrelated number-theoretic/analytic statements. S16 finds O2's interval reader; S17 finds the program permutation reader, both reused. Reading the remaining hits found only the disclosed relatives or unrelated uses. Maintainer D1, D2 and D4 probes are consistent with these searches; D3 has the domain defect stated above. No fresh Lean search probe was run.

**Counts: 0 blockers, 0 majors, 1 minor, 0 new notes. Prior resolved items are not counted again.**

**Verdict for PR #392: CLEAR.**
