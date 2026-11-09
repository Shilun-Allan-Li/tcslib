**lwe-sis-adapter-proofs-findings.md**

**Verdict: PASS for the frozen encoding-adapter proof gate.**

**Totals: 0 blockers, 0 majors, 0 minors, 3 continuing notes.**

I reviewed all 14 filled proofs, all 20 source declarations and adjacent sketches, the 284-constant inventory, and nine backing contracts. I found no mathematical defect, freeze violation, unsafe dependency, prohibited unfolding, or unsupported completion claim.

This was a static proof audit with independently executed integrity, freeze, dependency, axiom-accounting, style, and finite semantic checks. **I did not independently rerun Lean.**

| Item | Verified identity |
|---|---|
| Repository | `Shilun-Allan-Li/tcslib` |
| Exchange commit | `228c265d642013da76afa6cec976eaf11a8eb1b9` |
| Statement freeze | `6eec97be8f54d9990340900a5595dab32fb477f5` |
| Filled Lean/root | `b9ce3521e7f5a15d80e71bf5e9be4c48bc73010e` |
| Bundled records | `223713ba5ea15ac98dc5efedaad5a7208854e3d1` |
| Construction dependency | `690217cc1aaefe411158808a8b0797fd887a8abc`, PR #237 |
| PR / target | [#238](https://github.com/Shilun-Allan-Li/tcslib/pull/238) / `cryptography/lwe-sis-constructions` |
| Bundle SHA-256 | `24de3637321750a0ad12ec46120e32d28db102fd4cd77f0b56621e5e4bd16225` |
| Bundle bytes / sections | 5,711,128 / 1,009 |
| Lean / Mathlib | `v4.25.0` / `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e` |

I read the three requested READMEs in order, followed the first-section pack, and read the policy, workflow, campaign plan, five earlier findings reports, and their dispositions.

All five exchange checksums pass. Both revision-qualified indexes agree in every ordered entry; every section matches its indexed size and SHA-256. Independently retrieved, untruncated GitHub trees confirm that **all 101 source attachments and 908 records attachments match their stated revision/path Git blobs**.

All nested checksum sets pass: 146 current proof-fill entries, 199 adapter-statement entries, 174 construction-proof entries, 106 construction-statement entries, 86 representation-proof entries, 82 foundation entries, and nine continuation entries.

The baseline snapshot matches the independently retrieved statement-freeze source. Source comparison and full-diff examination confirm:

- Exactly the 14 previously admitted theorem bodies changed.
- All 20 ordered declarations, signatures, definition bodies, imports, options, namespaces, and attributes remain unchanged.
- The three complete equation proofs remain `rfl`, without new simp attributes.
- All 100 other frozen paths remain byte-identical.
- Across the library-source trees, only the adapter module changes.

The overview and two sketch corrections accurately describe the final implementation. This verifies source invariance; it is not an independently reproduced elaborated type-hash comparison.

Locations below refer to `TCSlib/Cryptography/Encoding/BinaryArith.lean`.

| Group | Source declarations | Filled proofs | Assessment |
|---|---:|---:|---|
| Forward conversion, lines 58–121 | 6 | 4 | Endian induction, numeric recovery, length bound, and efficiency composition are correct. |
| Width normalization, lines 123–195 | 6 | 4 | Canonical low-bit writing, exact width, matching-width preservation, and efficiency are correct. |
| Reverse conversion, lines 197–294 | 8 | 6 | Numeric writing, exact width, both round-trip formulations, modular recovery, and efficiency are correct. |
| **Total** | **20** | **14** | **3 definitions and 17 theorems; no remaining source admissions.** |

The forward induction correctly handles the empty word and both Boolean branches. Appending a bit to the reversed tail contributes precisely its positional power of two. The numeric recovery and length proofs then apply the existing public reader and normalization lemmas.

The all-zero reconstruction uses the correctly attributed `Candidates.listToNat_replicate_false`. The normalization proof applies the existing zero-prefix/drop identity without assuming that the payload fits. Its length calculation cancels the payload length over natural numbers; preservation uses exactly the matching-width hypothesis.

Reverse conversion derives its endian equality from the proved forward result and `bitsVal_bits`, without duplicating the induction or assuming numeral injectivity. The unconditional forward round trip returns width normalization. Exact recovery retains the original matching-width premise, including leading zeros. The converse returns normalized little-endian bits of the value modulo the target power of two.

Empty words, all-zero words, zero width, overlong payloads, arbitrary template contents, and malformed pairs remain covered. On malformed pairs, both total projections are empty, giving the zero word at the width evaluated at parameter zero.

All three efficiency proofs compose the following nine existing public contracts:

| Owner | Contracts |
|---|---|
| `Complexity.BinArith` | `polyTimeComputable_reverse`, `polyTimeComputable_normBits` |
| `TCSlib.Cryptography.EnsembleLemmas` | `polyTimeComputable_zeros` |
| `Complexity` | `polyTimeComputable_pairDropPoly`, `polyTimeComputable_pairFstD`, `polyTimeComputable_pairSndD` |
| `Complexity.PolyTimeComputable` | `comp`, `pairEncode`, `append` |

The normalizer correctly supplies the original payload as the drop-length template and zeros followed by that payload as the word being cut. Each polynomial is fixed before selecting the machine. No runtime arbitrary-polynomial evaluator, new host, handwritten helper, or copied infrastructure is introduced. The new proofs read foreign definitions through public equations; their sketches match the implemented steps.

The raw probe independently reconciles with the structured inventories:

| Check | Result |
|---|---:|
| Owned constants with only standard axioms | 284 |
| Earlier constants preserving identity and exact axiom sets | 263 |
| Statement-era constants preserving module, kind, and visibility | 283 |
| Source declarations agreeing with explicit axiom prints | 20 |
| Backing contracts agreeing with explicit axiom prints | 9 |
| Owned constants containing `sorryAx` | 0 |
| Unexplained additional constants | 0 |

The sole addition is
`TCSlib.Cryptography.Encoding.BinaryArith.normalizeWidthPoly_length._proof_1_1`.
It is the disclosed compiler-generated arithmetic theorem, using `propext` and `Quot.sound`. Every inventoried axiom set is contained in `propext`, `Classical.choice`, and `Quot.sound`.

I reconstructed the exact five-root, 93-module dependency closure and verified its topological order, source hashes, raw logs, and recorded outcomes. They reconcile to zero errors, zero owned admissions, 17 inherited admission warnings, and 194.383 seconds. All 92 inherited module logs match their statement-gate counterparts. The separate probe record reconciles to 29.042 seconds.

All nine development snapshots match their recorded hashes. Failed runs 00 and 07 retain their diagnostics separately; final run 08 matches the filled source. They are not substituted for final-sweep evidence.

I reran all five scoped style checks: **0 FAIL / 2 unchanged WARN over 19 files**. The eight scoped package revisions agree with the unchanged manifest. Physical package/cache provenance, isolation, fresh native objects, and actual execution remain maintainer attestations; no whole-library root elaboration is established.

Independent finite models passed 2,047 endian-word cases, 32,752 word/width scenarios, and 20,475 raw-word/polynomial scenarios, including 10,710 malformed-input scenarios. These supplement the general proof review and are not Lean execution.

| ID | Severity | Location | Evidence / finding | Required follow-through |
|---|---|---|---|---|
| N01 | Continuing note | `policy.md` §2; source-validation records | Full frozen-primary validation, reference ingestion, and approved matching remain open. Prepared source inventories do not establish closure. | Preserve the earlier findings and complete the applicable source-policy work. No adapter proof correction identified. |
| N02 | Continuing note | Proof-fill execution evidence; integration records | Supplied scoped evidence reconciles, but this reviewer did not rerun Lean. Native provenance/freshness attestations, 17 inherited warnings, and applicable landing checks remain. | Retain these limits and perform the relevant integration checks. The 14 adapter admissions are discharged in this reviewed fill. |
| N03 | Continuing note | Sampler, machine, and primitive consumer gates | These adapters do not complete actual-law sampling, implemented schedules, common-secret sample quantifiers, uniform negligible bounds, raw collision semantics, scalar/matrix implementations, or primitive-security bridges. | Carry those obligations into their consumer gates. No cryptographic hardness or completed security endpoint follows from this pass. |

**PASS closes only this frozen proof gate.** Source-policy work, applicable landing checks, and user-controlled integration remain outstanding. No repository files were edited, proofs filled, workers dispatched, pushes performed, or merges made.
