**lwe-sis-adapter-statements-findings.md**

**Verdict: PASS for the frozen encoding-adapter statement gate.**

**Totals: 0 blockers, 0 majors, 0 minors, 3 continuing notes.**

I reviewed all 20 adapter declarations, their prose and sketches, the three defining-equation proofs, all 14 admitted obligations, preservation of the 263 earlier constants, and the nine consumed machine contracts. I found no false statement, unsafe dependency, freeze violation, material API defect, or unsupported completion claim.

This was a static mathematical audit with independently executed integrity, inventory, dependency, semantic-model and style checks. **I did not independently rerun Lean. The 14 adapter obligations remain admitted.**

| Item | Verified identity |
|---|---|
| Repository | `Shilun-Allan-Li/tcslib` |
| Exchange commit | `a0b0d03b5694a0e9ab3df3ff6dfdd88ed7326ef4` |
| Frozen Lean/root | `6eec97be8f54d9990340900a5595dab32fb477f5` |
| Bundled records | `82f01285d688c09ddbce370a34f20944ba206fb6` |
| Audited stack baseline | `ff8345b1d2ac2f605d81cdf6c23216aadb918abb` |
| Draft branch / central target | `cryptography/lwe-sis-adapter-statements` / `cryptography/lwe-sis-constructions` |
| Bundle SHA-256 | `5b26dabb5fa78b2f79a778808e79f5483ff0d0b7beb1709af0aee4c86f705b76` |
| Bundle bytes / sections | 5,114,602 / 844 |
| Lean / Mathlib | `v4.25.0` / `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e` |

I read the three requested READMEs in order and followed the first-section pack. All five exchange checksums pass. Both revision-qualified indexes agree in all 844 ordered entries; every section matches its indexed size and SHA-256. Independently retrieved GitHub trees also confirm that **all 101 source files and 743 records files match their stated revision’s Git blobs**.

All nested checksum sets pass: 199 adapter-evidence entries, 174 construction-proof entries, 106 construction-statement entries, 86 representation-proof entries, 82 foundation entries and nine continuation entries. Earlier findings, resolutions and historical gate/fill records remain unchanged.

Adapter locations below refer to `TCSlib/Cryptography/Encoding/BinaryArith.lean`.

| Coverage | Declarations | Admissions | Assessment |
|---|---:|---:|---|
| `toLE` and its five theorems, lines 57–97 | 6 | 4 | Endian conversion, numeric reading, length bound and polynomial-time route are sound. |
| `normalizeWidthPoly` and its five theorems, lines 102–152 | 6 | 4 | Low-bit normalization, canonical numeral equation, exact width, preservation and polynomial-time route are sound. |
| `fromLEPoly` and its seven theorems, lines 157–225 | 8 | 6 | Reverse conversion, width, both round-trip formulations and polynomial-time route are sound. |
| **Total** | **20** | **14** | **3 definitions, 17 theorems; exactly 3 closed defining equations.** |

`toLE_eq`, `normalizeWidthPoly_eq` and `fromLEPoly_eq` state their complete definition bodies and are correctly proved by `rfl`. None introduces a simp attribute.

The endian sketch correctly relates the MSB reader to the LE reader of the reversed word using the existing append-singleton equation. Normalization then preserves the value and cannot increase length. The reverse-endian equality can be recovered from `toLE_eq_natBits` and `bitsVal_bits`, as sketched, without duplicating the induction.

Prepending the requested number of zeros and dropping the original payload length retains precisely the requested low bits. The canonical numeral equation therefore applies to overlong operands as well as shorter ones. Exact length and preservation at matching width need neither a numeric-fit hypothesis nor a positive-width hypothesis.

Reverse conversion reverses only the payload and reconstructs a valid pair with the original template. The forward round trip correctly returns width normalization; its stronger equality correctly requires matching original width. The converse correctly returns normalized LE bits of the value reduced modulo the requested power of two.

Empty words, all-zero words, leading zeros and zero width introduce no missing premise. Malformed pairs use the existing empty default projections, so normalization and reverse conversion return the all-zero word of width `p.eval 0`. Templates need not be unary.

Independent finite semantic checks passed 18,414 scenarios covering all bit strings through length nine, widths zero through twelve, and five polynomial templates, including malformed inputs. These checks supplement the general mathematical review; they are not Lean proofs.

The polynomial-time sketches use these nine separately probed public contracts:

| Namespace | Contracts |
|---|---|
| `Complexity.BinArith` | `polyTimeComputable_reverse`, `polyTimeComputable_normBits` |
| `TCSlib.Cryptography.EnsembleLemmas` | `polyTimeComputable_zeros` |
| `Complexity` | `polyTimeComputable_pairDropPoly`, `polyTimeComputable_pairFstD`, `polyTimeComputable_pairSndD` |
| `Complexity.PolyTimeComputable` | `comp`, `pairEncode`, `append` |

For width normalization, the original payload is the first component of the prepared pair, serving as the drop-length template; zeros followed by that payload form its second component. Its length on `pairEncode u w` is correctly `3 * w.length + p.eval u.length + 2`. Applying the existing polynomial drop at `.var` gives the specified output on every input. All three efficiency statements fix their polynomial before selecting a machine. No runtime-polynomial evaluator, new host or foreign-definition unfolding is required.

The full baseline-to-source Git-tree comparison contains exactly two changes: the new adapter file and the Encoding facade’s import/contents additions. All 99 other frozen files are unchanged. Root exports, owner APIs, pins and the proposed probability-reader patch are untouched.

The raw environment probe reconciles with every inventory row:

| Inventory check | Result |
|---|---:|
| Earlier constants preserving module, kind, visibility and exact axiom set | 263 |
| New constants, exactly matching source declarations | 20 |
| Total owned constants | 283 |
| New compiler auxiliaries or unexplained constants | 0 |
| New constants containing `sorryAx` | Exactly the 14 disclosed obligations |
| Backing contracts containing `sorryAx` or nonstandard axioms | 0 |

All earlier constants use only standard axioms. All 29 explicit axiom prints agree with the inventories.

I reconstructed the exact five-root, 93-module source closure and checked its dependency order, source hashes, raw logs and recorded execution metadata. They reconcile to zero errors, 14 new admission warnings, 17 inherited warnings and 181.289 seconds. The failed bootstrap and its pre-repair source remain separately identified and are not counted as passing evidence.

The five scoped style checks independently reproduce **0 FAIL / 2 unchanged WARN over 19 files**. The eight scoped package revisions agree with the unchanged manifest. All 720 previously selected cache keys agree with the new 721-module inventory. I independently retrieved the selected official archive and verified its recorded size and SHA-256. The Language source is identical at the pinned Mathlib revision and the disclosed producer revision. Physical isolation, compiled-content provenance and native freshness remain attestations.

The module explicitly identifies these interfaces as repository adaptations, with PS10 and AB09 supplying representation context. I found no new exact-textbook attribution claim or primitive-security completion claim.

| ID | Severity | Location | Evidence / finding | Required repair or follow-through |
|---|---|---|---|---|
| N01 | Continuing note | `policy.md` §2; prior source-review records | Full frozen-source validation, ingestion and approved matching remain open. Contextual citations do not close those obligations. | Preserve the earlier reports and complete the outstanding source-policy work before claiming closure. No adapter statement correction identified. |
| N02 | Continuing note | Adapter execution evidence; integration records | Supplied scoped evidence reconciles, but this reviewer did not rerun Lean. Fourteen adapter admissions, 17 inherited warnings, freshness/isolation attestations and landing checks remain explicit. | Retain these limits; discharge the adapter proofs through subsequent authorized work and perform applicable integration checks. |
| N03 | Continuing note | Future machine and primitive consumers | These adapters do not establish actual-law sampling, sufficient common-secret sample schedules, uniform negligible bounds, raw collision semantics, complete scalar/matrix implementations or primitive security. | Carry those obligations into their consumer gates. No hardness conclusion follows from this pass. |

**PASS closes only this frozen statement gate.** Proof completion, source-policy closure, landing checks and user-controlled integration remain outstanding. No repository files were edited, proofs filled, workers dispatched, pushes performed or merges made.

Notation: `p` is the fixed polynomial; `u` the parameter template; `w` the payload.
