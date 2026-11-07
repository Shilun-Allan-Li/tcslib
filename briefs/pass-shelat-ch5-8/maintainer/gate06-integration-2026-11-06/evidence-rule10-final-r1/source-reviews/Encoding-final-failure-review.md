# Encoding: final source-identity witnesses

**Two failing declarations / two diagnostics; both complete header/proof blocks are unchanged. Both exact historical keys already exist.** No new Encoding cleanup key is proposed, and neither newly added decoder reader is a failing declaration. Every diagnostic remains retained; this is not acceptance, a pass, an exclusion or a waiver.

Exact pins: base `eee107e92a7db11f1f8c98a5c2867304f57ddc54`, head `3f6db40e1688c4a0bb922c9575dd3bd2157a650b`.

`TCSlib/Cryptography/ZeroKnowledge/Encoding.lean` base SHA-256 is `ee5b3a7fc84e24346c0a71a99b1b724746d8c653e986b866cde4b4f9e0177db7`; head SHA-256 is `a2a354fd0a89b117022922f416b431a26393b207dbf65e72c4f9a6e3c4247ddc`. Removing the eight-line `decGraph_eq`/`decGraph_fst` insertion (head 134–141) reproduces the **whole base file byte for byte**. All prior definitions, proof headers/bodies, docstrings, formal/deviation prose, options, imports and scope/binding commands are unchanged.

| Declaration in `TCSlib.Cryptography` | Complete base block | Complete head block | Failing source / probe | Native log line | Historical exact rows |
| --- | --- | --- | --- | ---: | --- |
| `two_pow_size_le_two_mul_succ` | 492–495 | 500–503 | 503 / 553 | 688 | `cleanup-b-decls.tsv`:314; `cleanup-b.tsv`:157 |
| `polyTimeComputable_encPermFromCoins` | 631–688 | 639–696 | 695 / 745 | 694 | `cleanup-b-decls.tsv`:313; `cleanup-b.tsv`:158 |

Raw complete-block SHA-256 respectively:

- `09805ae0b121deb5126f803b3f0732df20b5b8664a97a32118cf5dbdbf709c27`.
- `f50e9c1a0566c0c523b2d95eb9b29b251e46df7d28c58bb7438e5a563985e41f`.

The first failure is the unchanged conversion from the bound stated using `permBits n` to the goal using `Nat.size n`. The second is the unchanged final reflexivity conversion between numeric samplers parameterized by `permBits`/`permTrials` and by `Nat.size`/`2*n*n`. The log shows those unreduced foreign aliases directly. No new proof or algorithm regression is indicated by these diagnostics; no repair is proposed in this review.

## Operative context

Both versions use `namespace TCSlib.Cryptography` and `open Complexity Turing`; the scoped `open EncodingMachines in` of the second proof is also identical. The new decoder-reading theorems have no simp/instance attributes and are not named by either failing proof. The local decoder, encoders, coin table and surrounding quantitative bounds keep their original bodies and contracts.

Of the 38 TCSlib source files in the current import closure, 37 are fully byte-identical. The only changed file is `InformationTheory/FinDist.lean`: it adds documentation and the acceptance-probability API (`FinDist.probTrue`, `probTrue_sub_probTrue`, `probTrue_eq`). Removing its insertions reproduces its entire base source; no existing definition, datatype, theorem body or attribute changes. Neither failing proof refers to the new API. In particular, the pure schedule/numeric-sampler operation contracts do not depend on that acceptance-probability addition.

The operative homes `Asymptotic/Permutations.lean`, `ZeroKnowledge/EncodingPermutations.lean` and `ZeroKnowledge/EncodingMachines.lean` are all byte-identical. This checks the actual `permBits`/`permTrials`, permutation sampler and numeric sampler contexts, rather than assuming semantic identity from unchanged identifier spellings. Exact source fingerprints, changed FinDist insertions and both raw proof blocks are in the JSON. Compiler/package source configuration is the same final base/head configuration already checked in the companion PolyTimeModel review; no base native rebuild is claimed.

Both historical keys match the same source path and exact source name. The historical seal rows even identify the corresponding old failure lines 495 and 687. They should receive fresh observation links, not duplicate debt keys. Inventory SHA-256 pins are `371988e791191772c9c74b6d86879b2b688cba731dbd0f3dc4c5decc3411f6fb` (`cleanup-b-decls.tsv`) and `32d88f9f3ff992ba4b46033d8800e199b48fd5f7416a59e1d6aa1dee088cac92` (`cleanup-b.tsv`). This module adds no new key to the frozen 764 inventory.

## Evidence and limits

Read the completed `G06Seal_039_TCSlib_Cryptography_ZeroKnowledge_Encoding.classification.json`, SHA-256 `7965c6aa158f0f2df58f8685e7e23eaea2040f64074ecb087b5e7704b63ba042`, and referenced native log SHA-256 `888fc4c2a874cede10bf25b5ad346a1ce02ff126f38988b76593cbcb64825440` as data. It records rc1, two source diagnostics and no fresh object. Own read-only checks matched their coordinates/maps, all 684 actual-name/home/status installation rows and the 684-name EOF marker. Reversing the probe insertions recovered exact head source; probe SHA-256 is `2bb10755d8b6aa8d32ab7c450bbe67717465ae0ab95a1f297b386dc6393843a5`.

No repository helper or native/cache/build/app command was executed. Only independently authored read-only Git/text analysis and temporary review-artifact writes occurred; no library, Git, final scratch or campaign evidence was changed. JSON SHA-256: `467316e45ddfb8470a317c2c263fa0212f610146df284428b2b2ee0a3c8c2a75`.

**Not yet clear to merge — both failures remain retained and require root's final observation/ledger reconciliation.**
