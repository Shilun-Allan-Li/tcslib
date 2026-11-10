# Gate 13 rank, gadget, and recovery proofs

Draft [#250](https://github.com/Shilun-Allan-Li/tcslib/pull/250) targets
`cryptography/lwe-sis-constructions`. The seven fills at `713093c36ac66f7e56e9354581f0bb3f59772341` join
the two checked rank proofs at `75a4214dc098cd6c363d00c34f569bac23eb4555` for one independent review.

| Pin | Revision |
|---|---|
| Passed Gate 12 round-two Lean and root | `93dc88648f117877e42aaf58ba7b911c76a4b63a` |
| Rank records and restored checkpoint baseline | `d34b0e409bc179167921073a731a0eb3e009f267` |
| Approved shared reader commit | `2414fd3eae05c99474d1888609b01ac5989523a5` |
| Checked Lean and root | `713093c36ac66f7e56e9354581f0bb3f59772341` |
| Central preview target | `41aaf0a1acf29318fa8d741dadd9f5f585e43c93` |

| Scope | Checked result |
|---|---|
| `AllButOne.AntiCyclic` | Reindex the cyclotomic power basis and cancel multiplication by a nonzero element to prove the integer rank results. |
| `Lossy.Gadget` | Read each binary block as its positional sum and identify the single contributing block in the transposed gadget product. |
| `Lossy.Matrix` | Cancel the concealed product, round the encoded digits under the strict error bound, and invert block packing in the injective mode. |
| `AllButOne.Basic` | Cancel the two encoded branch shifts. The strict bound makes equal decoded residues lift to equal integer products. Integer rank and digit injectivity give non-designated branch injectivity. |

The user approved the exact four-line `Randomized.blockVal_eq` patch.
The non-simp owner equation is isolated in its own commit and uses no axioms.
The seven consumer bodies use public reader and algebra contracts. The
positional-sum proof reindexes directly by the slice length and coordinate
equations. The rank checkpoint contains the two precise Mathlib imports.
There are zero copied proof lines and zero new helper declarations.
[Approved reader proposal](../../gates/08-construction-statements/proposed-random-bits-reader.patch)

| Verification | Result |
|---|---|
| Source freeze | All 220 prior declarations preserve their signatures. Five Lean paths changed from Gate 12 and 148 frozen paths are byte-identical. |
| Native sweep | 144 modules across seven facades, 420.500 s, zero errors. |
| Admissions | Nine owned and 17 inherited warnings. Other warning payloads match Gate 12. |
| Axiom probe | 329 explicit prints, 616 inventoried constants, 84.134 s. All nine fills use only standard axioms. |
| Type probe | All 220 representations exactly match the rank checkpoint, 3.352 s. Four earlier representation changes retain the recorded kernel equalities with Gate 12. |
| Style | Zero failures and two inherited warnings over 41 files. |
| Merge preview | Tree `997489939120a1c1f5221a3a9780671beedf23f7` preserves the checked library, root and pins. |

Lean emits the existing `Lossy.evaluate.congr_simp` auxiliary in
`Lossy.Matrix`. Gate 12 recorded its origin in `AllButOne.Basic`. Its name, kind, visibility and axiom set match Gate 12.
[Axiom delta](evidence/axiom-delta.json)

The restored source ran on arm64 macOS with Lean 4.25.0 and the existing
manifest. The per-module script built a fresh object tree using this
worktree's pinned package cache. The 178 restored rank source and object
fingerprints recheck. The evidence covers the campaign closure. Whole-library
elaboration remains a landing check. [Cache receipt](evidence/cache-provenance.json)

The finite results use the existing dyadic adaptation of PW10 §§6.3.2–6.4.
Scoped source matching remains open. The nine counted-loop and CRH obligations
await the separate shared host disposition. Efficient all-but-one inversion,
signature and CCA2 bridges, and family-level security endpoints remain separate.
[Rank report](../08-anti-cyclic-rank/REPORT.md) · [PW10 source manifest](../07-sis-trapdoor/pw10-primary-source.json)

**Not yet clear to merge.** The combined proof audit and remaining landing
requirements are open.
