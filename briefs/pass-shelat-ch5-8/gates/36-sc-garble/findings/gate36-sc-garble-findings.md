# Pass–shelat Gate 36 — sc-garble

**Verdict: HOLD.** **0 blockers, 1 major, 0 minors, 0 notes.** The seven target proofs and B2 survive this source/evidence audit. G36-01 is an undisclosed re-proof of an existing public lemma, which the dispatch explicitly grades as a major.

| Pin | Audited revision |
|---|---|
| Repository / PR | `Shilun-Allan-Li/tcslib` / draft [#323](https://github.com/Shilun-Allan-Li/tcslib/pull/323) |
| Lean head | `cd9a48438c2a6548fe9e246ce569be57c9df96b3` |
| Lean tree | `13aa553d035fd55cf73c7123ebb73c1940019f1c` |
| Landing base | `1321b9cb358867f5b51974b8c5d0781519a9cfdb` |
| Campaign records | `fb18d199fdce1f8cd1ae94ea9e092c52b157ce86` |
| Exchange | `ab34c528748af26491d896e0f504373b45e4ada1` |

I read the pinned README, pack, bundle, changed sources, relevant providers, rulings and evidence. I reran byte, archive, declaration and scope checks against git objects, and checked the supplied build/seal records against their raw logs and source/probe hashes. **I did not execute Lean:** this environment has no Lean/lake toolchain. Kernel-build and seal outcomes below therefore describe verified supplied evidence, not an independent compilation.

**Finding**

| # | Severity | File · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|
| G36-01 | **major** | `SecureComputation/SpecialEncryptionMulti/SliceParser.lean:119–126`, `SliceReduction.length_le_encodeList` | Re-proves the existing public `TCSlib.Cryptography.length_le_length_encodeList` on precisely the same encoder and domain, without disclosing that overlap. | `Asymptotic/BlockEncryptor.lean:53–76`; worker report, “Overlap and reuse”; DL-46/DL-47. See `evidence/G36-01-source-excerpts.txt`. | Remove the new duplicate and use the existing public lemma in `slicePost_encode`'s fuel bound; import its provider and rerun the affected checks. |

Paths in this finding are under `TCSlib/Cryptography/`.

The equality of the statements is exact after resolving the existing file's `open PrivateKeyScheme (encodeList)`:

```lean
-- New: SecureComputation.SliceReduction.length_le_encodeList
-- Existing: TCSlib.Cryptography.length_le_length_encodeList
(l : List (List Bool)) → l.length ≤ (PrivateKeyScheme.encodeList l).length
```

The existing theorem is public and byte-identical at both the issue base `fbd37f44…` and the audited head. Both proofs induct on `l`, use the encoder's nil/cons equations and the pairing length formula, and finish with arithmetic. This is not merely a similar bound for another carrier.

The worker report instead identifies the private `ETTGame.length_le_length_encodeLog` and the structured-history bounds `EffFill.length_le_length_encodeHist` / `length_encodeLog_le` as the nearest relatives. It does not identify this exact public theorem. The review's duplication search repeats those relatives and misses it. DL-46 covers the `encodeList_eq_flatMap` copies and named related material; DL-47 covers getD/headD copies, including SG-F04. Neither lists this length-bound duplicate. Those dispositions therefore do not discharge G36-01.

A direct replacement at the use in `slicePost_encode` is:

```lean
have h := TCSlib.Cryptography.length_le_length_encodeList (l.map Prod.snd)
```

The current import graph has no path from `Asymptotic/BlockEncryptor.lean` to `SliceParser.lean`, so importing that provider introduces no import cycle. This proposed repair has not been compiled here. Update the overlap report and declaration inventory after removing the duplicate; keep every frozen declaration unchanged.

**Proof audit**

The source comparison used [PS10, §§6.2.2–6.2.3](https://www.cs.cornell.edu/courses/cs4830/2010fa/lecnotes.pdf), Algorithm 157.2 and the extra wrong-key property, together with the frozen interfaces and the pack's stated deviations. The formal garbling conclusion is correctness of the first successful opening; its weaker relationship to the book's unique-opening wording is already disclosed.

1. **`spDecStr_wrongKey` — correct.** `spDecStr_none_iff_prefix_ne` proves that honest ciphertexts pass all length guards and failure is exactly inequality of the two pad prefixes. `hG'.easy` supplies the efficient evaluator used by the test; the conclusion's potentially inefficient `E'` is needed only on canonical inputs, where `hGE'` specifies the same family. The reduction uses D3's one-query machine and D1 at budget one. Conditional on the nonce and independent comparison key, a random-function answer has a uniform `n`-bit prefix, so acceptance is exactly `2⁻ⁿ`. The PRF advantage plus `2⁻ⁿ` bounds prefix collision; one further positive `2⁻ⁿ` gives the frozen strict inequality. At `n = 0`, both prefixes are empty and the extra positive term still gives strictness.

2. **`specialScheme_wrongKey` — correct.** The new key/nonce equivalences preserve their encoded strings. The public activation readers identify the scheme's algorithms with string encryption/decryption, and `uprob_fst` averages away decryption coins. String failure produces a word of length `n+1`, so `decodeFin n` returns `none`. Monotonicity transfers the strict string bound to the required scheme event.

3. **`specialScheme_multiMessageSecure` — correct and directly from D4.** The proof invokes `MultiMsg.exists_negligible_distAdv_prfEncRealOut` in `SpecialEncryptionSecurity.lean`, with full-width masks `0^n ++ m_i`. The shared zero-prefix identity identifies each encoded ciphertext after the key/nonce coin equivalence. `acceptProb_comp_equiv` transports both acceptance probabilities. The proof does not depend on downstream B1 or `specialScheme_multiMessageSecure_of_joint`; the import graph confirms the required direction.

4. **`nestedSpecial_wrongKeyBot` — correct.** The two string bounds give success errors whose nonnegativity is derived from probability nonnegativity. With zero positions there are no distinct assignments. With one position the independent key/nonce marginal gives the inner bound. With two positions, a different first choice permits conditioning on the inner ciphertext and applying the outer bound; an equal first choice opens the outer layer correctly and leaves a different second choice for the inner bound. `length_nestedInner` supplies the exact inner message length. Adding the unused nonnegative error gives `ε₁ + ε₂` in both cases.

5. **B2 and `uprob_not_good_le` — correct.** The B2 header equals the binding draft after whitespace normalization. `IsFaninTwo` supplies distinct argument vertices and arity at most two; `args_lt` separates them from the output vertex. The published restriction/evaluation laws therefore give the independent plaintext key, argument-key table and row coin required by `WrongKeyBot`. Correctness opens the intended row; permutation surjectivity places it in the table, and absence of cross-openings determines the first successful value. The number of ordered distinct assignment pairs is `2^arity * (2^arity - 1)`, namely `0`, `2` or `12`. Two finite union bounds give the required coefficient. Cross-opening events ignore row order, so the uniform-data theorem legitimately allows seed-dependent permutations. Fixed-permutation B2 is its identity-map specialization; the frozen uniform-seed theorem averages B2 over permutations, rather than repeating its proof.

6. **`yaoSeed_good_whp` — correct.** The key blocks lie below `2*sizeBound`, and the row-half blocks begin there and lie below `10*sizeBound`; the block-index injection and the bounded, injective assignment fold establish disjointness. Restricting the raw bit table gives the joint uniform key/row-coin law, including zero-length bit blocks. The stronger uniform-data theorem applies to the actual XOR-shift permutations without an independence requirement. Each output collision has probability `2⁻ⁿ`; a union bound over output positions remains valid when vertices repeat. The final error is exactly the stated polynomial multiple of the nesting error plus `outLen(n)*2⁻ⁿ`, and is negligible.

7. **B1, `sliceMultiMessageSecure_of_prfOut` — correct.** Offsets and lengths are bounded by the polynomial output width, and both dependent message vectors range over finite types. Maximizing over `Option (Pack n)` with `none` valued at zero implements the empty-fit-set convention. The maximizing slice descriptors have polynomial-length unary advice. `slicePost` is total and polynomial-time on arbitrary words through the existing iterate-and-emit host and its state-length bound. `slicePost_tuple` establishes the exact same-seed identity with the slice ciphertexts through the published tuple, real-sampler and mask readers. The NUPPT composition/advice API gives the postprocessed distinguisher with a coin equivalence. D4 chooses its negligible bound before the masks; `distAdv_comp` and coin invariance transfer it to the maximizing pair, which dominates every fitting choice. If the maximum is `none`, applying D4 to equal zero masks proves the required nonnegative error bound. This also handles a zero maximum when fitting configurations exist.

Gate 27 obligations (1)–(6) are met respectively by the maximizing advice, the efficient parser and its same-seed law, the full-pad random-function law already inside D2/D4, D4's triangle bound, the direct D4 proof of the frozen scheme theorem with the still-proved downstream corollary, and B2. No hybrid or random-function proof is reconstructed in B1.

The remaining edge cases are covered without strengthened hypotheses: `ℓ(n) = 0` or `< n`, `q(n) = 0` (one ciphertext), empty messages, exact fits including Yao's outer slice, arities zero/one/two, constant gates, zero-argument XOR shifts, zero gates, and coinciding outputs.

**Integrity, Rule 10 and documentation**

| Check | Result |
|---|---|
| Pack `SHA256SUMS` | **21/21 verified**, using the exact exchange git objects. |
| Nested manifests | `verification.zip`: 147 files, exactly 146 manifest paths plus the manifest; review archive: 1201 files and 72 directories, exactly 1200 manifest paths plus the manifest. Every hash verifies. |
| Sources and diff | All **166** source files equal pinned head blobs. All 14 source-head hashes, line counts and width counts verify. `pr.diff.txt` equals the base-to-head git diff: 14 files, +1901/−122. |
| Public statements | Replayed decls2: **55 ADDED, 0 CHANGED, 0 REMOVED**. |
| Frozen declarations | Replayed the inspected supplied checker against git blobs: **0 unexpected differences** over 139 owned-file and 72 DAGCircuit base declarations. |
| SG-1 | Exactly **six private removals**, zero changed surviving headers/definitions; the one-character `of_joint` header control and seventh-removal control each reproduce exactly one difference. Private-name uses at the issue base are confined to `SpecialEncryptionMulti.lean`. `of_joint` keeps its entire docstring and header. |
| Other proofs and Yao restriction | **126** other surviving pre-existing theorem/lemma declarations remain byte-identical. Yao has exactly the three permitted hunks: the target's result bullet, sketch and body; no import changes. |
| SG-F01 | DAGCircuit has exactly the approved nine added lines, no removals; the new reader is `Iff.rfl`. Its sealed negative/reader control bites as required. |
| LE-doc | Exactly three files; deleting doc comments makes each pre-edit/head pair byte-identical. The added result entries and sketch sentence describe the delivered code. |
| Canonical coe-A seals | Supplied results: **14/14 head, 6/6 base pass**. Strict A has the same pass counts. |
| Seal coverage | Rechecked all four variants at base/head: exact eligible closure rows, every collected term reference covered or explicitly excluded as notation/reducible/abbreviation, correct source reconstruction from recorded insertions, matching source/probe hashes, and complete install/EOF verification. Every run records `maxErrors = 0`. |
| Seal B / SG-F07 | **30 head errors versus 21 base errors**. The nine new errors are the disclosed `PolyExpr.eval` conversions: 1 in GarblingSecurity, 1 in NestedBounds, 2 in SpecialEncryptionSecurity, 5 in WrongKey. Raw diagnostics agree with the attribution; no additional forbidden-definition read was found. `of_joint` passes all variants. |
| Paired controls | Canonical: **24 probes, 43 sealed negatives**, each negative fails once and readers pass. Strict: **28 probes, 57 negatives**; the only reader failures are the 14 disclosed `ctlCoeReader` failures. |
| Axioms | The seven targets, B2, the two stronger uniform-data endpoints, `garbling_good_whp` and `of_joint` have exactly the standard three axioms in the supplied census. Of 531 stored constants, only the three disclosed Yao-hybrid admissions retain `sorryAx`. |
| Build evidence | Rechecked **388 build + 9 edit-build records**, their raw log hashes and zero-error fields. The last build source hash of every one of the 388 distinct modules equals its final-head blob. These are supplied compilation results. |
| Documentation/API | New public definitions have readers; the two Prop-valued “NO-FORMULA” rows do state their formulas. The supplied 21 long-proof sketches match the inspected proofs. No additional formula/sketch defect was found. |

The disclosed DL-46/DL-47 material, including SG-F04, is not re-raised. SG-F02, SG-F03/LE-doc, SG-F05, SG-F06 and SG-F07 retain their stated dispositions. G36-01 is additional to those dispositions.

The merged-tip integration rebuilds with #313, #318, #319 or #324 remain the maintainer's pending merge conditions, as instructed. Dispatch and merging remain with the user.

The accompanying ZIP contains this Markdown and the auditor's hash results, statement/control replays, scope checks, source excerpts and build/seal evidence checks. **Gate 36 remains HOLD until G36-01 is resolved.**

Glossary: `n` is the security parameter; `ℓ` is the polynomial output/message-width expression at the relevant declaration; `q` is the polynomial ciphertext budget minus one; `arity` is a gate's number of arguments; `ε₁, ε₂` are the inner/outer string success-error bounds. All declaration names and other parameters are those of the pinned source.
