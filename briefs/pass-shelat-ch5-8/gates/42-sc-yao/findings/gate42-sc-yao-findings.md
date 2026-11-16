# Gate 42 — sc-yao proof audit

**Verdict: HOLD — one major duplication finding and two documentation minors.**

| Severity | Open findings |
|---|---:|
| Blocker | 0 |
| Major | 1 |
| Minor | 2 |
| Note | 0 |

Audit of [draft PR #341](https://github.com/Shilun-Allan-Li/tcslib/pull/341), conducted on 16 November 2026. The accepted exceptions and resolved historical findings below are not counted again as open findings. Dispatch and merge remain with Seyoon; the separately running integration build remains a maintainer merge condition.

## Pins and method

| Material | Commit |
|---|---|
| Exchange pack | `747b61e7d95d44461639c5884aed33aa4908fc00` |
| Audited Lean head | `e9b03c437aca251846430ff23b40ee5ff3d3347a` |
| Campaign records | `f22e0f6798815b9263893e61928b4f16452f74ee` |
| SY-F01–03 rulings | `67423db6c9d6448ae531b04f42c315585d00d502` |
| DL-49 wording correction | `d6fe1ddd4f38b9bd29d2c707dcb4b60129b4586e` |
| SY-F05 remainder / DL-52 | `bf08dbfa3a057a3b41d20f6dbede3066bc5e6660` |

I independently checked the pack's 22 SHA-256 entries, all 248 manifested entries of `verification.zip`, and all 1,510 manifested entries of the separately retrieved review-evidence ZIP, including exact archive path sets. Its SHA-256 is `d3f7c3da0d081acd9275e798514fffd7b538c83787a109c11c59bab4e2c3b5a8`. All 103 bundle sections match their named source blobs/files, allowing the bundle's separating newlines. All 262 Lean files in the supplied source closure match Git blob identities at the audited head. The supplied PR diff matches an independently generated diff, fixing Git's hash abbreviation width.

The worker's 7,597-entry top-level manifest has exactly the committed delivery's path set. The pack's full worker-byte verification records were inspected; this audit did not independently stream every worker blob again. I reviewed the proof chain and recounted the supplied build, axiom and seal evidence; **I did not run a fresh Lean build or new seals**.

## Open findings

Helper paths below are relative to `TCSlib/Cryptography/SecureComputation/Yao/HybridProof/`.

| ID | Severity | File / declaration | Claim and evidence | Proposed fix |
|---|---|---|---|---|
| G42-01 | **major** | `RunWithHost.lean:88` `acc_poly` | This re-proves public `Complexity.StateLoop.MajLoop.acc_poly` (`TCSlib/Complexity/Randomized/Build/StringLoops.lean:144`) for exactly the same word predicate. The predicates at `RunWithHost.lean:69` and `StringLoops.lean:97` both return `decide (pairFstD (pairSndD w) = [])`; their public readers identify the functions pointwise. The new body re-assembles the same polynomial-time proof from `polyTimeComputable_isNil` and pair projections. `StringLoops.lean` and `Repetition.lean` are byte-identical between the issue base and the head, and `RunWithHost` already imports `Repetition`, which imports `StringLoops`. Thus SY-5 does not apply and no extra import is needed. The REPORT does not disclose `MajLoop`; DL-49/51/52 and the later rulings do not cover this overlap. SY-F06 mentions the predicate coincidence but misses the matching public efficiency theorem. | Preserve the helper API and derive `acc_poly` from `MajLoop.acc_poly` through the two public readers, then refresh the required checks. Alternatively, obtain an explicit ruling accepting this exact duplication as ledger debt. |
| G42-02 | minor | `ChunkScanner.lean:28`; `GarblingProgram.lean:27` | The first module's references section uses `[AB09, §6.2]` without a full AB09 bibliography entry. The second cites `[BMR90]` in `tables_poly`'s docstring, but its references section lists only PS10. These are bibliography omissions, not fabricated tags. | Add the full AB09 and BMR90 references to the respective module docstrings. |
| G42-03 | minor | `Yao.lean:863` `yaoHybrid_polyTime`; `SelectedLaw.lean:69` `acceptProb_fill`; `FakeSimulatorFactory.lean:83` `exists_data`; `SeedCoordinates.lean:239` `pick_iff_place`; `FakeProgram.lean:227` `tables_poly`; `BobIO.lean:99` `outputBit_poly` | These six proofs have at least 40 proof lines and no internal step comments. Their sketches exist, but the brief's “long proofs get step comments” requirement and policy §3 also require comments connecting major proof blocks to those sketches. This is the unresolved documentation component of SY-F09. | Add brief comments at the proof's major boundaries. Keep statements and proof terms unchanged. The unnecessary-`simpa` warning remains informational. |

A proposed proof-only replacement for G42-01 is below. It uses the existing import closure and published readers, preserving the statement. This candidate was not elaborated in this audit:

```lean
theorem acc_poly : PolyTimeComputable fun w => [acc w] := by
  simpa only [acc_eq, Complexity.StateLoop.MajLoop.acc_eq] using
    Complexity.StateLoop.MajLoop.acc_poly
```

This finding concerns reuse discipline, not the mathematical validity of the current efficiency proof. No mathematical gap in the two frozen targets was identified.

## Proof assessment

1. **Efficiency.** `yaoHybrid_polyTime` supplies both efficient main strategies, both call-input machines and the answer-independent message envelope through `HybridProtocol.polyTime_iff`. The strategy contracts quantify over arbitrary words and histories. The description decoder is correct on every canonical circuit description and polynomial-time on all strings. The evaluator handles arbitrary received table/answer words, with a polynomial bound on every encoded prefix state. Fixed assignment enumerations are handled by finite, constant-arity branches; no efficient computation of `Finset.univ.toList` is assumed.

2. **Statistical simulation.** The copying simulator for Alice and the output switch for Bob use the same bad-seed bound from the unchanged `yaoSeed_good_whp`. The two components of `yaoHybrid_correct` supply the required outputs off that event. Tape equivalences preserve the actual tape words, and unused independent tapes are removed through published marginal identities.

3. **Exact endpoints.** `CoinSeedRelabel.seed_relabel` and `BobStageZero.acceptProb_eq_stage0` transport the entire tape, including unused coordinates and XOR shifts. `SamplerEndpoints.acceptProb_end_eq_ideal` identifies the last stage with the fixed fake simulator. The proof does not replace the actual row-order distribution by a uniform permutation distribution.

4. **B1 embedding / Gate 27 obligations.** `GateOccurrences` enumerates selected inactive-key occurrences across all gates and proves exhaustion, uniqueness and the four-per-gate bound. `SelectedRows` implements both slice shapes: the only/inner case fits because `0 + n + n = 2n`; the outer case fits because `2n + n + (4n + 2) = 7n + 2`. `SelectedStep.advice_next` fixes identical advice on both sides. Acyclicity, distinct gate arguments and sink outputs supply symbolic label separation. `SelectedTables` proves pointwise reconstruction, and `SliceReconstruction.rebuild_poly` supplies a total polynomial-time reconstruction. `SelectedAdviceBounds` bounds all retained advice. All five Gate 27 obligations are discharged; no adaptive ciphertext-dependent challenge messages are required.

5. **Quantifiers and total error.** Both simulator machines are fixed before the distinguisher. `SliceReduction.reconstruction_negligible` selects one worst finite advice option per parameter, producing one negligible bound covering every input, selected substep and baseline tape. `SelectedLaw.acceptProb_fill` justifies averaging back to the actual tape law. The gate chain and `simulators_of_output_switch` yield the bound

   \[
   \delta(n)+2S(n)\lvert\mu(n)\rvert,
   \]

   negligible by the published closure lemmas. Empty circuits use the optional empty advice choice and require no selected wire. Zero key width, empty input/output lists, zero/one/two-argument gates, repeated sink outputs, unused coordinates and coincident key values introduce no extra hypothesis. A repeated argument within one gate is excluded by the frozen fan-in predicate; a wire used at different positions in different gates is covered by the all-occurrence construction.

The proof establishes the frozen OT-hybrid statements. Its fake-garbling/topological-hybrid architecture agrees with the cited [Lindell–Pinkas proof, pp. 180–184](https://www.cs.columbia.edu/~tal/6261/SP16/LP_yao.pdf). The PS10 excerpt supports Protocol 162.6, Definition 155.1 and Theorem 163.7. Bit transfer, XOR row order, sink outputs, output decoding and the joint PRF hypothesis remain explicitly documented deviations. No fabricated new source tag or PS10 locator was identified; the `.a` locators are the disclosed inventory labels for unnumbered source passages.

## Frozen files and landing edits

- `Yao.lean`: all 76 declarations remain in order. Outside the six approved regions and LE-title, the file is byte-identical to the base. Target headers, statement prose, `include` prefixes and `yaoSeed_good_whp` are preserved. The head has 1,179 lines, within SY-2's 1,200-line cap.
- `Uniform.lean`: removing exactly the seven approved formula-docstring `rfl` readers restores the base byte for byte. No attributes are attached to them. `DAGCircuit.lean` is unchanged against the tip.
- The other 68 changed paths are the new hub and its helpers. The hub imports its 67 children. No additional frozen file changes.
- LE-bullet and LE-title have their stated scope. LE-reuse derives the two assignment-fold results directly from `GarblingProbability.assignmentFold_small`, preserving their headers and imports. Independently stripping comments from all 64 LE-doc files gives identical code before and after the commit.
- All 739 new public declarations have docstrings. No further material formula or sketch mismatch was identified. G42-02 and G42-03 remain documentation cleanup items.

## Rule 10 and build evidence

| Check | Audited evidence / result |
|---|---|
| `Yao.lean`, seal A | 0 errors, coe and strict. |
| `Yao.lean`, seal B | 24 errors in each variant; 15 inherited and 9 new. The new 2 efficiency and 7 simulator-body errors are `PolyExpr.eval` index/type conversions or their cascades. No additional forbidden read was identified. |
| `Uniform.lean` | The same 4 errors in the same two inherited declarations at base and head; the new readers pass. |
| Helpers | All 68 canonical coe-A seals pass; all 15 sampled other-variant seals pass. The recorded 272 worker seals support the wider coverage. |
| Probe identity | Independently removing the seal harness reproduces the audited code of all 71 canonical probe owners, modulo comments and blank lines. |
| Controls | Independently recounted: coe 83/83 negative declarations fail once, 15 unsealed files pass; strict 100/100 negatives fail once, 17 unsealed files pass. The strict `ctlCoeReader` failures are exactly the recorded projection-coercion harness effect. |
| Explicit reads | Reviewed the 1,512-reference scan and its 28 local-name candidates; no uncovered foreign-definition unfold identified. |
| Build | Recounted 718/718 successful module checks with 0 `error:`/`error(` diagnostics; checked raw-log hashes against run records. The recorded whole-order check is 1,356/1,356. |
| Axioms | The three audited Yao results and `yaoSeed_good_whp` report only `propext`, `Classical.choice`, `Quot.sound`, with no direct `sorryAx` user in their closures. The recorded 1,492-constant census has no nonstandard axiom. |

The old build's `yaoProtocol_hbcSecure` admission is traced solely to then-unmerged `hbcSecure_compose`. It does not hold this OT-hybrid audit. The integration build with #324/#327 remains outside the audit, as instructed.

## SY-F01–SY-F12 grades

| Item | Grade / disposition | Reason |
|---|---|---|
| SY-F01 | Resolved by confirmation | The four approved imports serve range assembly, `dbl_append`, the expectation coupling inequality and the encoding identity. Their uses match the recorded requests; no additional unapproved helper import was identified. |
| SY-F02 | Accepted debt, DL-51 | The named statistical-switch declarations and DDH relative match the code. Without the ruling, the undisclosed re-proof would be major, not minor. The ruling permits promotion and re-pointing later. |
| SY-F03 | Accepted debt, DL-49 extension | Both `encodeMsgs_eq_encWords` copies and the flat-map relative match. The two proofs/statements agree up to bound-variable names; their docstrings differ. Apply the wording correction. Without the ruling, the undisclosed overlap would be major. |
| SY-F04 | Fixed | LE-doc is comment-only; formula coverage is restored. G42-02 concerns separate file-level references. |
| SY-F05 | Fixed / accepted debt | Assignment-fold reuse is fixed. DL-52 correctly records `OTAnswerWords.length_answersB:41` / `answersA_nil:94` against #324's `length_answersB:60` / `length_answersA:52`, using output lengths one and zero. Re-point after #341 merges, per the later ruling. |
| SY-F06 | **Regrade the loop-efficiency overlap to major** | G42-01: the matching `MajLoop.acc_poly` makes this an undisclosed re-proof of an already public lemma, beyond a predicate-name resemblance. The scanner generalization, fixed-test fiber inequality and chain-bound reuse remain notes. |
| SY-F07 | Agree: note | Canonical seals pass on the touched proof code; the seal-B and inherited Uniform failures are correctly attributed. |
| SY-F08 | Agree: note | The inline Mathlib lookup rewrites are expressly permitted. No new DL-47-shaped theorem was identified. The differing rewrite counts use different counting conventions. |
| SY-F09 | **Regrade step-comment omission to minor** | G42-03. The linter warning remains a note. |
| SY-F10 | Agree: note | Both hosts have public generic same-machine correctness/time/head contracts and draft promotion requests, as SY-4 permits. Promotion remains a maintainer decision. |
| SY-F11 | Agree: note | Uniformity is proved for both actual simulator constructions; the frozen statement need not be strengthened. |
| SY-F12 | Agree: accepted size exception | 1,179 ≤ 1,200; no size or width excess elsewhere. |

DL-49, DL-51 and DL-52 correctly identify their declarations and required cleanup. The newer rulings supersede the pack's stale “still open” language. G42-01 is outside those rows and keeps the gate open. No concrete #324/#327 name interaction was identified.

## Notation

`n`: security parameter; `S(n)`: polynomial circuit-size bound; `δ(n)`: negligible bad-seed bound; `μ(n)`: the single negligible B1 reduction bound for a fixed distinguisher.
