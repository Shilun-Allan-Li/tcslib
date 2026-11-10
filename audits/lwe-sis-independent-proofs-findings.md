# Independent LWE/SIS construction proof fill — round 1 findings

**Verdict: PASS for the frozen 31-proof gate, with one documentation minor.**

**Totals: 0 blockers, 0 majors, 1 minor, 4 continuing notes.** The earlier statement-gate F01 repair is verified. N01–N04 remain in force; F02 below is the new minor.

I reviewed all 31 filled proofs in seven modules and their adjacent sketches, preservation of all 220 ordered source declarations and 62 earlier closed source readers, the complete 589-constant inventory, and all 48 backing contracts. I found no invalid proof, changed mathematical interface, prohibited unfolding, unsafe dependency, or material completion overclaim. Seventy owned admissions remain outside this gate.

**This was a static proof audit with independently executed integrity, source-comparison, inventory, dependency, and style checks. I did not rerun Lean.** Lean and Lake are unavailable in this reviewer environment. Native execution, physical object freshness, package/cache provenance, and isolation remain maintainer attestations.

| Item | Inspected identity |
|---|---|
| Repository | `Shilun-Allan-Li/tcslib` |
| Exchange branch / commit | `exchange/pass-shelat-ch5-8` / `8efc0e669ed3ed004616c4aab81317ebf5fa17e6` |
| Statement freeze | `17b2a282b545c6ebca3fccc88d518d18ae78f485` |
| Statement F01 comment repair | `f1b75a7d17dc7ef5fddd7403a2d7c740ba365c9c` |
| Passed-gate/doc-repair baseline | `13aff4d33d282ccaed2727af3febc0ebddeba0e5` |
| Filled Lean/root | `f293b63200ee3c6de6e709925f67c4d60fdc7b4a` |
| Bundled records | `ebb0422cd08c44494b3b0c76020de18492cb8ff7` |
| PR / target | [#250](https://github.com/Shilun-Allan-Li/tcslib/pull/250) / `cryptography/lwe-sis-constructions` |
| Audited dependencies | PRs #236, #237, #238, #239 |
| Bundle SHA-256 | `c7837eb73e59a5d0ee0cdda33ae275bb096e80715a10f3f6f1b84004d921d675` |
| Bundle bytes / sections | 43,628,531 / 2,796 |
| Lean / Mathlib | `v4.25.0` / `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e` |

I read the three requested READMEs in order and followed the first-section pack, including policy, workflow, the campaign plan/current records, and all nine earlier findings with their separate dispositions. Live PR metadata confirms the draft and central target. This verdict concerns the immutable source and records above.

All five exchange checksums pass. Both ordered revision-qualified indexes agree exactly, and every section passes its byte-length, SHA-256, and framing checks. Independently retrieved, untruncated Git trees authenticate **all 153 source and 2,643 record attachments** against their specified revision/path Git blob identities. All **12 nested checksum sets, totaling 2,411 entries**, pass; the current proof-evidence set contains 326 entries. All nine earlier findings and nine separate resolutions match the passed-gate/intake baseline.

An independent comment-aware comparison confirms the complete 19-module surface retains its 57 definitions, 163 theorem statements, declaration order, imports, options, attributes, and namespaces. Exactly 31 former `by sorry` bodies change. The 62 earlier closed readers remain the same complete `rfl` proofs; all 70 remaining admission bodies remain unchanged. There is no added handwritten declaration, helper, instance, host, or copied proved infrastructure.

Full library-tree comparison against the proof baseline identifies precisely the seven disclosed proof files, with no added or removed Lean paths. All other frozen paths, shared owner APIs, registry, policies, root/facade exports, toolchain, and fifteen package pins remain unchanged. The six earlier export overlaps remain a separate statement-stage landing concern; this fill adds none.

The statement-freeze-to-baseline library diff consists solely of the BooleanVector overview repair. Its comment-stripped code is identical. The replacement correctly describes the existing public counted loop, its pending registry disposition, and paused dependent FP fills. The retained repair snapshot and successful module/style records agree; no registration or shared-owner exception was applied.

Paths below are relative to `TCSlib/Cryptography/`.

| Module | Filled proofs | Assessment |
|---|---:|---|
| `Encoding/DyadicUniform` | 9 | Canonical numeral recovery and cardinality give scalar bijectivity; coordinatewise assembly gives vector/matrix bijections. Public finite-bijection sums establish the actual uniform pushforwards. Encoding recovers every original block in the declared order. |
| `LWE/BitNoise` | 4 | Probability counts all seed preimages. Both integer bit counts lie between zero and the block width. Complementation negates their difference and preserves the law; coordinate permutations independently prove zero mean. |
| `LWE/Sampling` | 3 | The product equivalence changes only the matrix and common-secret blocks, retaining every original row-noise seed. Pushforward equality and public acceptance averaging preserve independent distinguisher coins. |
| `Encryption/PublicKey/Regev/Basic` | 4 | Public matrix/dot-product identities cancel the common-secret term, retaining the original integer error sum. Subadditivity and Boolean cases give its natural absolute-value bound; the strict decoder premise yields every-coin correctness. |
| `Pseudorandom/Generators/LWE/Basic` | 5 | Public advantage equations and the existing DLWE assumption give the conditional transfer. Both cardinalities charge the complete seed/output spaces; stretch cancels only the common matrix budget. |
| `Pseudorandom/Generators/LWE/Bits` | 3 | Length and seed cardinality are exact. The concrete faithful encoder's injectivity and output cardinality give a bijection onto all output words; real and ideal relabelings retain every test coin. |
| `Pseudorandom/Generators/LWE/Flat` | 3 | Existing explicit little-endian equivalences relabel the original seeds and full uniform outputs. Advantage and both length identities preserve the complete budgets. The stale overview is F02. |
| **Total** | **31** | **No mathematical repair identified.** |

The dyadic arguments cover width zero/modulus one and empty dimensions wherever their types permit them. The noise arguments cover the empty seed and preserve multiplicities rather than replacing the law by uniform support. The mean proof does not duplicate the symmetry proof. Integer/real casts and the finite-sum cancellation are consistent.

Regev correctness uses the stated strict comparison with half the modulus rounded down. It does not replace that condition with an informal quarter-modulus estimate or a probabilistic tail bound. The keygen corollary applies the support bound to each original noise seed.

The bit-generator proof constructs an equivalence from the actual encoder; it does not substitute an arbitrary-choice generator program. Its length casts reconstruct the same list. The sibling flat generator retains its explicit little-endian convention, distinct from the MSB challenge codec. No exact-seed asymptotic PRG compiler, efficient family sampler, or completed encryption/security interface follows from these identities.

All selected proofs consume foreign definitions through public equations or contracts. Explicit simplification of proof-local lets is permitted; Matrix/function-space `change` steps use allowed core/Mathlib reduction. The five revised sketches accurately describe their implemented routes. The remaining twelve modules and their admissions preserve the passed statements and readiness boundaries.

| Inventory check | Independently reconciled result |
|---|---:|
| Earlier audited foundation/core/adapter/scalar constants | 302 |
| Combined statement source declarations | 220 |
| Original generated non-simp projection readers | 40 |
| Original compiler auxiliaries | 13 |
| New compiler auxiliaries | 14 |
| **Total owned constants** | **589** |
| Owned constants containing `sorryAx` | Exactly the 70 intentional remaining obligations |
| Other owned constants using only standard axioms | 519 |
| Backing contracts using only standard axioms | 48 |
| Explicit source/backing axiom prints reconciled | 220 / 48 |

The raw environment walk, all 268 explicit axiom prints, and structured inventories agree. Every selected fill and new auxiliary uses only `propext`, `Classical.choice`, and `Quot.sound`, or a subset thereof. No selected fill depends on a remaining admission. The original 575-constant inventory also matches its historical raw probe; precisely the selected 31 earlier axiom sets change. All previous kinds and visibilities remain fixed.

The two disclosed compiler-emission changes are `DyadicUniform.bitsToVector.congr_simp` and `DyadicUniform.bitsToMatrix.congr_simp`: their originating module changes from Sampling to DyadicUniform. Their names, kinds, visibility, axiom sets, and recorded elaborated types remain identical. The other 573 earlier module origins are unchanged. All fourteen additions are accounted-for compiler auxiliaries, without a new handwritten declaration.

I independently parsed both supplemental raw type-probe logs and compared the exact level-parameter/type-expression representations for **all 575 previous names**; every pair agrees, and the recorded hashes reconcile. These logs come from separate supplied imported-object environments. The baseline used the maintainer's preserved audited objects, not a fresh rebuild of that historical revision. This comparison is neither reviewer-native execution nor a whole-library type certificate.

I reconstructed the exact seven-facade **144-module** closure and checked its topological order, all final source snapshots/hashes, raw logs, admission counts, and serial timing records. They reconcile to zero errors, **70 owned plus 17 inherited admission warnings**, and **303.792 seconds**. The final axiom probe reconciles to **53.149 seconds**. All **144 non-admission warning messages** match the statement baseline separately. The thirteen development runs, including their failures and fourteen module snapshots, retain matching source hashes and diagnostic counts; they are not substituted for final evidence.

All eight independently rerun scoped style checks reproduce **0 FAIL / 2 unchanged WARN over 41 files**. The warnings are the existing assumption-acronym reader cases. Earlier finite models were retained; I did not rerun them for this proof-only change. Whole-library root elaboration remains unclaimed.

The statement findings archive matches its disclosed **13,818-byte** retained-text hash, `8588df8f02701a29cf9ca3332759985d8ba26ef0d57360657927ab4ea8bad345`. Original native metadata reported 13,819 bytes and raw download failed. I preserve that distinction; original-file byte identity is unverified.

| ID | Severity | Location | Evidence / finding | Required repair or follow-through |
|---|---|---|---|---|
| F02 | Minor | [`Pseudorandom/Generators/LWE/Flat.lean:27`](https://github.com/Shilun-Allan-Li/tcslib/blob/f293b63200ee3c6de6e709925f67c4d60fdc7b4a/TCSlib/Cryptography/Pseudorandom/Generators/LWE/Flat.lean#L27) | The module overview still says “Nontrivial claims remain admitted.” All three formerly admitted obligations in this module are filled and axiom-clean. This is stale completion prose. | Correct that overview in a separate comment-only repair and verify unchanged code. No proof or statement change is indicated. |
| N01 | Continuing note | `policy.md` §2; source-validation/ingestion records | Full frozen-primary validation, ingestion, and approved matching remain open, including PW10. Prepared proposals and this proof review do not close source policy. | Preserve the earlier findings and complete the applicable source-policy work. |
| N02 | Continuing note | Final sweep/probes; provenance and landing records | This reviewer did not rerun Lean. Seventeen inherited admissions, physical/native/cache/freshness attestations, the historical-object limitation of the type comparison, report-byte provenance, and applicable integration checks remain explicit. | Retain these limits, reconcile the dependency stack/export overlaps before landing, and preserve user approval of all merges. |
| N03 | Continuing note | Sampler/schedule, machine, and primitive consumers | These 31 fills discharge their selected obligations only. Efficient uniform schedules/noise implementations, required common-secret quantifiers, uniform message bounds, machine/game bridges, exact-seed PRG integration, all-but-one inversion, strong one-time signatures, and final CCA2 remain separate. SIS hardness stays independent. | Carry each obligation into its relevant gate. No hardness reduction or completed primitive-security endpoint is certified. |
| N04 | Continuing readiness note | `COORDINATION.md`, `FILL_READINESS.md`; unapplied reader/catalogue proposals | The missing random-bit/probability readers and counted-loop registry/host-gate disposition remain unresolved. This fill neither applies the proposals nor bypasses their holds. Seventy remaining admissions include held routes and later independent work. | Keep affected routes paused pending the relevant owner/registry and host-gate disposition; retain any applicable head-envelope requirement. This PASS authorizes no shared-owner patch or policy exception. |

**PASS closes only this frozen 31-proof review.** F02 needs its local documentation repair. The seventy remaining admissions, N01–N04, source-policy and landing work, and user-controlled merge approval remain. No repository source or records were edited, proofs filled, workers dispatched, pushes performed, or merges made by this audit.