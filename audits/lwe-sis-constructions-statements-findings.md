# LWE/SIS combined construction statements — round 1 findings

**Verdict: PASS for the frozen combined statement gate, with one documentation minor.**

**Totals: 0 blockers, 0 majors, 1 minor, 4 notes.** N01–N03 are retained; N04 records the narrower proof-readiness disposition.

I reviewed all 19 mathematical modules in full, all 220 source declarations and their prose, all 101 admitted obligations/sketches, all 62 closed source readers, 40 generated readers, 13 compiler auxiliaries, the complete 575-constant inventory, and all 48 backing contracts. I found no false statement, missing mathematical hypothesis, unsafe axiom dependency, or undisclosed mathematical-interface change.

**This was a static mathematical audit with independently executed integrity, inventory, dependency, style and finite-model checks. I did not rerun Lean. All 101 obligations remain admitted.**

| Item | Inspected identity |
|---|---|
| Repository | `Shilun-Allan-Li/tcslib` |
| Exchange branch / commit | `exchange/pass-shelat-ch5-8` / `64e245b345d908d835030efede1c91312a4e6cce` |
| Frozen Lean/root | `17b2a282b545c6ebca3fccc88d518d18ae78f485` |
| Mathematical commit | `2bf9dd52882bcafbce9eab48a5bab796275f2094` |
| Bundled records | `03f13bc817f4d281801e2025d3722bcab513c6c0` |
| Audited stack baseline | `307cfdd1d6cadfda2ae9cca5367705ad770c5f42` |
| Last audited Lean dependency | `ec72ed773a690c17ac253707350935cc9e0acb34` |
| PR / target | [#250](https://github.com/Shilun-Allan-Li/tcslib/pull/250) / `cryptography/lwe-sis-constructions` |
| Audited dependency PRs | #236 / #237 / #238 / #239 |
| Bundle SHA-256 | `04b19eff425cc268426662a4352f2be4cfa96a97d965a559c1f82f2e51444d8d` |
| Bundle bytes / sections | 18,418,400 / 2,395 |
| Lean / Mathlib | `v4.25.0` / `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e` |

I read the three requested READMEs in order and followed the first-section pack, including policy, workflow, campaign plan, all eight earlier findings and their separate resolutions. PR metadata confirms the draft and target; this verdict applies to the frozen identities above.

All five exchange checksums pass. Both ordered revision-qualified indexes agree exactly in revision, path, length and SHA-256. Every section passes its length, hash and framing checks. Independently computed Git blob identities match the pinned repository trees for **all 153 source and 2,242 record attachments**. All ten nested checksum sets pass, including 1,018 current evidence entries. The eight earlier findings and eight resolutions remain identical to the stack baseline.

| Reviewed slice | Modules | Declarations | Admissions | Assessment |
|---|---:|---:|---:|---|
| Dyadic uniform sampling, bit-noise laws, common-secret sampling | 3 | 35 | 16 | Exact laws retain noise-seed multiplicities, one secret and independent row seeds. |
| Encoded dot/matrix products and Boolean expansion | 2 | 34 | 20 | Total framing, fixed widths, growth bounds and fixed-polynomial FP routes are sound; catalogue hold retained. |
| SIS universality, raw collision output, implementation and asymptotics | 4 | 29 | 19 | Composite-modulus universality, strong extraction and the integer collision reduction have the required premises. |
| Regev PKE algorithms and experiments | 2 | 31 | 10 | Transpose orientation, strict correctness margin and concrete hybrid constants are correct. |
| Structured, MSB and flat direct generators | 3 | 31 | 11 | Full seed accounting, explicit equivalences and advantage identities are correct. |
| Lossy and all-but-one mathematics and concealer hybrids | 5 | 60 | 25 | Rounding, cancellation, integer image bounds and bounded-lifting injectivity are sound. |
| **Total** | **19** | **220** | **101** | **57 definitions and 163 theorems reviewed.** |

The dyadic bijections include width zero/modulus one and empty dimensions wherever their types allow them. Centered noise uses its actual two-block bit law, with bounded support, reflection symmetry and zero mean. Neither finite seed cardinality nor exact sampling at one parameter establishes an efficient uniform family sampler.

The arithmetic loops consume the actual MSB chunks. A short chunk has implicit leading zeros; replacing this by flat end-padding would change its value. The unconditional output-length and growth statements cover malformed nested pairs, short/excess words, leading zeros, zero counters and zero widths. The retained-context bound with constant eight supplies the advertised nine/two loop envelope. The FP sketches use existing public contracts and fix their polynomial schedules before choosing machines.

For SIS, a differing Boolean coordinate gives an integer coefficient of +1 or −1, which is invertible modulo every allowed modulus. This supports collision universality without primality, pairwise independence or a hardness assumption. Strong extraction includes the public seed and uses the full output cardinality. The raw adapter preserves false-padding/splitting and writes the actual integer difference using the existing sign/magnitude codec. Its encoder equality correctly includes magnitude width zero; exact decoding correctly requires positive width. The asymptotic route uses `NUPPT.exists_compParam`, preserving advice and coins, with explicit column, norm, width and independent `SISAssumption` premises.

Regev cancellation retains the original integer subset-error sum. Its magnitude is bounded by sample count times the entry bound, and the stated strict separation supports every-coin correctness through the existing decoder. Augmentation is a bijection onto the full matrix with one additional row. Consequently extraction charges `q^(dimension+1)`, and the final bound contains both DLWE advantages and twice the extraction error. The noise law and common secret are preserved.

Generator budgets charge the public matrix, secret and every noise-seed bit. The stretch criterion correctly cancels only the common matrix budget. The MSB challenge codec and the flat generator’s existing little-endian equivalences are explicitly distinguished. Neither the advantage identities nor cardinalities provide the remaining exact-seed asymptotic PRG or efficiency bridge.

The trapdoor statements use strict dyadic rounding and an ordinary secret matrix. Lossy image counting factors through the first modular product and the bounded **integer** error vector. Each concealer hybrid replaces one column with a standard challenge having exactly the original sample count; simulated columns have independent secrets/noise and share the challenge matrix. The two public translations give the two displayed sums of DLWE advantages.

The anti-cyclic definition’s wrapped `Fin` subtraction and below-diagonal sign match the stated polynomial multiplication route. Power-of-two width gives integer injectivity through the rational quotient by the irreducible polynomial. For all-but-one evaluation, the larger message modulus exceeds twice the absolute branch-message bound. Equal rounded residues therefore lift to equal integers before applying injectivity. No modular-unit premise is silently substituted.

I compared the relevant primary passages in [Pei16 §5.2.1](https://web.eecs.umich.edu/~cpeikert/pubs/lattice-survey.pdf), [Wu24 Lecture 21](https://www.cs.utexas.edu/~dwu4/courses/sp24/static/notes.pdf), and [PW10 §§6.2–6.4](https://sites.cc.gatech.edu/fac/cpeikert/pubs/lossy_tdf.pdf). Their subset-sum, concealer-column and anti-cyclic architectures agree with the disclosed adaptations. This live comparison does not complete frozen-primary validation, ingestion or approved matching.

| Inventory check | Independently reconciled result |
|---|---:|
| Earlier constants retaining module, kind, visibility and exact axiom sets | 302 |
| New source declarations | 220 |
| Generated non-simp projection readers | 40 |
| New compiler auxiliaries | 13 |
| **Owned constants** | **575** |
| Owned constants containing `sorryAx` | Exactly the 101 intended source obligations |
| Remaining owned constants using only standard axioms | 474 |
| Backing contracts using only standard axioms | 48 |

All 268 explicit source/backing axiom prints agree with the raw environment walk and structured inventories. There are no unexplained constants or private-type derived instances. The foreign-qualified `ZMod.finEquiv.congr_simp` is correctly attributed to the new flat-generator module and uses only `propext` and `Quot.sound`. The 62 closed source proofs are complete `rfl` readers; all 40 generated readers use explicit non-simp configurations.

Complete Git-tree comparison confirms exactly 19 new mathematical files, six new facades and six modified export files. The mathematical and export commits are separate. The six existing-file diffs contain export/documentation wiring only; all other old library Lean files, owner APIs, registry, policy and pins remain fixed. All 153 freeze entries match. This is source-level invariance, not a reproduced elaborated type-hash certificate.

I reconstructed the exact seven-facade, 144-module closure and checked its topological order, final source snapshots, raw logs and serial timing records. **`evidence/audit-final-sweep/`**, after the reader refinement, reconciles to zero errors, 101 new and 17 inherited admission warnings, and **288.743 seconds**. The final probe reconciles to **44.702 seconds**. Earlier failed runs and the superseded `final-sweep` remain separately identified. The reader refinement changes no mathematical definition body or nontrivial statement.

I reran all eight scoped style checks: **0 FAIL / 2 unchanged WARN over 41 files**. The fifteen manifest pins and the eight-directory provenance receipt agree. The recorded 8,235-file source comparison does not authenticate native objects; physical package/cache origin, isolation, freshness and execution remain maintainer attestations. Whole-library root elaboration is unclaimed.

The supplied finite model was rerun with every recorded count reproduced, covering malformed framing/growth, dot and matrix products, Boolean expansion, signed output, strict rounding, gadget inversion, image budgets, rational anti-cyclic ranks and all-but-one evaluations. Additional exact checks passed **5,572 Regev residual cases and 20 neighboring-column endpoint-law comparisons**, retaining a 3:1 noise-seed multiplicity. These are supporting finite checks, not Lean proofs or general efficiency/security proofs.

| ID | Severity | Location | Evidence / finding | Required repair or follow-through |
|---|---|---|---|---|
| F01 | Minor | [`Encoding/BooleanVector.lean:26`](https://github.com/Shilun-Allan-Li/tcslib/blob/17b2a282b545c6ebca3fccc88d518d18ae78f485/TCSlib/Cryptography/Encoding/BooleanVector.lean#L26); `COORDINATION.md`; `INTERNAL_REVIEW.md` | The overview still says the sketch uses “a registered host.” The counted loop is public and proved but its registry row remains unapplied. The preparation records say this registration wording was removed. | Replace the stale phrase with the existing public counted-loop description and its pending registry disposition. Reverify this comment-only repair and record the correction; no theorem change is indicated. |
| N01 | Continuing note | `policy.md` §2; source-validation/ingestion records | Full frozen-primary validation, reference ingestion and approved matching remain open, including PW10. Earlier source-registry proposals remain unapplied. | Preserve earlier reports and complete the applicable source-policy work before claiming closure. |
| N02 | Continuing note | Final execution/probe evidence; integration records | Static evidence reconciles; this reviewer did not rerun Lean. All 101 admissions, seventeen inherited warnings, physical/native attestations and applicable landing checks remain explicit. | Retain these limits, complete separately reviewed fills and integration checks, and preserve user-controlled merging of the dependency stack and PR #250. |
| N03 | Continuing note | Sampler/schedule, machine and primitive consumer gates | This draft states substantial actual-law, arithmetic and concrete-security prerequisites. Efficient uniform schedules/noise implementations, required sample quantifiers, uniform message bounds, primitive bridges, exact-seed PRG integration, all-but-one inversion, strong one-time signatures and final CCA2 remain separate. SIS hardness stays independent. | Carry these obligations into the relevant proof and consumer gates. No completed primitive-security endpoint or hardness reduction follows from this statement pass. |
| N04 | Readiness note | `COORDINATION.md`, `FILL_READINESS.md`, both new patch/JSON proposals; earlier probability-reader proposal | Both new proposals’ baseline and proposed hashes reconcile in memory; neither is applied. `blockVal_eq` is missing. The existing loop’s functional/FP contracts are proved and adequate for the stated time-only routes, but catalogue registration and its absent separate head-envelope clause require disposition. Earlier `isUniversal_iff`/`hasMinEntropy_iff` readers are also still proposed. | **Narrow disposition:** mathematical statement review passes; affected reader/FP fills remain paused. Obtain the relevant owner/registry and host-gate disposition before those fills; retain any applicable head-envelope requirement. This audit approves no shared-owner edit or registry exception. |

**PASS closes only the frozen combined statement review.** The documentation minor needs correction and verification, and the stated proof-readiness holds remain in force. No repository source/records were edited, proofs filled, workers dispatched, pushes performed or merges made. The user alone approves and merges PRs.
 
Notation: `q` is the modulus; FP denotes polynomial-time function computability.
