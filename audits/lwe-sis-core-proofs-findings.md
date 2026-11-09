**lwe-sis-core-proofs-findings.md**

**Verdict: PASS for the frozen construction-core proof gate.**

**Totals: 0 blockers, 0 majors, 0 minors, 3 continuing notes.** I reviewed all 31 filled proofs, all 62 source declarations, their adjacent sketches, and the 263-constant axiom inventory. I found no mathematical defect, freeze violation, unsafe dependency, prohibited unfolding, or unsupported completion claim.

This was a static proof audit with independently executed integrity, freeze, inventory, dependency, and style checks. **I did not independently rerun Lean.**

| Item | Verified identity |
|---|---|
| Repository | `Shilun-Allan-Li/tcslib` |
| Exchange commit | `aaeb9b3764e7fa3c2d4f3e93905e8654ea1786f5` |
| Statement freeze | `a1f1b2e0d9315dff2a8dc36e2a6f8339c0a5abdf` |
| Filled Lean/root | `690217cc1aaefe411158808a8b0797fd887a8abc` |
| Bundled records | `42a400a1b88eecf9172a91ba287894450c72f9b0` |
| Audited dependency | `0769cba3e44c56700349f954190fc99d9e622270`, PR #236 |
| Construction PR / target | [#237](https://github.com/Shilun-Allan-Li/tcslib/pull/237) / `cryptography/lwe-sis-constructions` |
| Bundle | `lwe-sis-core-proofs-r1-bundle.md` |
| Bundle SHA-256 | `aacf0fbca7b937172888910ac1eb7129a294cdcd3280661842042f2a940f658e` |
| Bundle size / sections | 4,108,601 bytes / 593 |
| Lean / Mathlib | `v4.25.0` / `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e` |

I read the requested READMEs in order and followed the first-section pack. All five gate checksums pass. Both revision-qualified indexes agree in all 593 ordered rows, and every section matches its indexed size and SHA-256. I independently fetched every indexed file at its stated revision: **all 76 source files and 517 records files match the bundle exactly.**

All nested evidence checksum files pass: 174 current proof-fill entries, 106 statement-gate entries, 86 representation-proof entries, and 82 foundation entries. The three historical findings reports retain their recorded intake hashes.

Paths below are relative to `TCSlib/Cryptography/`.

| Module | Definitions | Theorems | Filled proofs | Assessment |
|---|---:|---:|---:|---|
| `Encoding/ModularDecode` | 2 | 10 | 5 | Both round-trip directions, canonical rejection and row-major indexing are correct. |
| `LWE/BitEncoding` | 3 | 9 | 6 | Minimal-lift distance arguments and strict bounded-error decoding are correct. |
| `Encryption/Symmetric/Regev/Basic` | 3 | 3 | 2 | Cancellation preserves the actual row error; correctness covers every seed. |
| `Encryption/Symmetric/Regev/Experiments` | 1 | 3 | 3 | Same-coin sampler identity, translation bijection and two-advantage bound are correct. |
| `Hashing/SIS/Basic` | 2 | 8 | 6 | Integer differences, norm/kernel conditions, compression and existence are correct. |
| `Hashing/SIS/Experiments` | 1 | 2 | 1 | Same-seed event inclusion gives the stated probability bound. |
| `Hashing/SIS/Profiles` | 2 | 8 | 8 | Constructor bounds, induction, compression, exclusion and bit budgets are correct. |
| `LWE/SampleSchedules` | 3 | 2 | 0 | Unchanged; sample bookkeeping and assumption scope are preserved. |
| **Total** | **17** | **45** | **31** | **All 62 declarations reviewed.** |

The independent freeze comparison reproduces exactly 31 changed theorem bodies, precisely the previously admitted targets. Declaration order, signatures, definition bodies, attributes, namespaces and names are unchanged. All 68 other frozen files match their baseline hashes. The only added code outside proofs consists of the three permitted imports: the list big-operator lemmas in `ModularDecode`, and `Linarith` and `Ring` in `Profiles`. Each already appears in the earlier 2,334-module cache inventory. This is a comment-stripped source comparison, not an elaborated type-hash comparison.

The parser proofs recover blocks through prefix lengths and public slicing equations. Successful parsing supplies canonical representatives and exact total length; reconstruction uses `List.ofFn_mul` without dividing by width. Both matrix proofs use the same row-major index. Modulus one, zero width, empty dimensions and range rejection introduce no missing premise. Encode-after-successful-decode correctly requires no global width-coverage hypothesis.

The distance proofs use the pinned public minimal-lift APIs. Exact half-modulus separation and the triangle inequality establish unique nearest-codepoint decoding under the stated strict bound, for both Boolean branches and either error sign. False-on-ties behavior is preserved. Encryption correctness then cancels the matrix-secret product and applies that decoder coordinatewise.

The encryption sampler identity retains the same matrix, common secret and row seeds. The ideal translation equivalence has valid left and right inverse proofs; `acceptProb_comp_equiv` also preserves the independent distinguisher coins. The final bound uses the real absolute-value triangle inequality with the existing advantage convention. It assumes neither uniform errors nor an efficient implementation.

The SIS difference is formed over integers before reduction. Distinct inputs give a nonzero difference, including at modulus two; each coordinate square is at most one. The column-budget hypothesis supplies the norm condition, and `Matrix.mulVec_sub` supplies the modular kernel equation. Pigeonhole uses the exact finite cardinalities. The probability proof compares events on the same matrix/finder-coin pair.

The dyadic induction starts at parameter zero and preserves the strict squared-norm inequality. The divisible-coordinate argument first extracts a nonzero coordinate from solution nonzeroness, then contradicts the norm budget. The input and output budgets follow the existing family readers. No hardness conclusion is inferred.

All 31 adjacent proof sketches match their implementations. I found no foreign definition passed for unfolding, new handwritten helper or host, or copied proved infrastructure. The disclosed local matrix flattening calculations apply the public identity directly.

The raw probe independently reconciles with all 62 source axiom prints and all 263 unique owned constants:

| Inventory category | Count |
|---|---:|
| Unchanged foundation constants | 166 |
| Source declarations | 62 |
| Generated non-simp readers | 23 |
| Earlier compiler auxiliaries | 5 |
| New compiler auxiliaries | 7 |
| **Total** | **263** |

Every inventoried axiom set is contained in `propext`, `Classical.choice`, and `Quot.sound`; none contains `sorryAx`. All 256 earlier constants retain their recorded module, kind and visibility; the 166 foundation constants retain their exact axiom sets.

The seven additions are accounted for: six arithmetic/index proof auxiliaries and `LWE.decisionAdvantage.congr_simp`. The latter is recorded by its originating Regev experiments module despite its LWE-qualified name. No unexplained constant remains.

I reconstructed the five facade roots’ exact 68-module dependency closure and verified the supplied sweep order, source hashes, raw logs and warning counts. The records reconcile to zero errors, zero owned admissions, 17 unchanged inherited admission warnings, and 189.926 seconds. The final axiom probe reports successful fresh output. All 42 development logs remain separately identifiable.

I reran the five scoped style checks: **0 FAIL / 2 unchanged WARN over 18 files**. All eight declared package revisions agree with the unchanged manifest and prior archive attestation. Physical isolation, package contents and native freshness remain maintainer attestations; whole-root elaboration remains unclaimed.

I independently compared the retrievable Pei16 SIS, binary-collision and common-secret DLWE passages. The squared-norm formulation, binary restriction and sample orientation are disclosed adaptations consistent with those passages. [web.eecs.umich.edu](https://web.eecs.umich.edu/~cpeikert/pubs/lattice-survey.pdf?utm_source=chatgpt.com) Complete frozen-PDF verification remains open; Wu24 retrieval timed out during this audit.

| ID | Severity | Location | Evidence / finding | Required repair or follow-through |
|---|---|---|---|---|
| N01 | Continuing note | `policy.md` §2; source-ingestion records | Exact primary acquisition is recorded, but validation, ingestion, approved matching and complete frozen-source comparison remain open. This audit did not rehash the complete PDFs. | Preserve prior reports and complete those source-policy obligations before claiming closure. No proof correction identified. |
| N02 | Continuing note | Proof-fill execution evidence; root exports | The scoped evidence reconciles, but this reviewer did not rerun Lean. Native freshness and isolation remain attestations; 17 inherited warnings and relevant integration checks remain. | Retain these limits and perform the applicable landing checks. |
| N03 | Continuing note | Sampler, machine and primitive consumer gates | These 31 admissions are discharged. Actual-law samplers, efficient adapters, common-secret sample quantifiers, uniform negligible message bounds, raw collision-output semantics, primitive bridges and independent SIS hardness remain separate obligations. | Carry these obligations into their consumer gates. No present semantic repair identified. |

**PASS applies to this frozen proof gate.** Source-policy work, relevant integration checks and the user’s PR approval remain outstanding. No repository files were edited, proofs filled, workers dispatched, pushes performed or merges made.
