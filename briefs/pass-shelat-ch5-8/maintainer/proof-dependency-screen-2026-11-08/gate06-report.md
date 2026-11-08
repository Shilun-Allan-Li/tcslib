# Strict Gate06 proof dependency screen

**No eligible proof target: all 33 direct sorried theorems are blocked by the full cleanup scope.** No proof work or new PR is authorized by this screen. The earlier comparison against 122 delivered changed paths is insufficient for the user's stricter authorization.

Frozen source: `3f6db40e1688c4a0bb922c9575dd3bd2157a650b` (Git tree `66057d9d810599f591883368ab447717117c6c76`). Cleanup roles come from the issued `role-manifest.json`, SHA-256 `6e9a80b270fe3459f54f38a2a2412c3e29fe64a7bf0a4ca64951e3e3157736a2`, at ancestor `1aa5506f58f77c215e56d24311ec33bd931cacf1`. It has exactly **97 CONSUMER + 124 PROVIDER_ONLY = 221 blocking paths**, plus two CHECK_ONLY aggregates. Provider-only paths block just as consumer paths do.

| Prong | Direct admitted theorem targets | Eligible | Blocked |
|---|---:|---:|---:|
| Authentication | 4 | 0 | 4 |
| SecureComputation | 13 | 0 | 13 |
| Composability | 13 | 0 | 13 |
| Randomness | 3 | 0 | 3 |
| Total | 33 | 0 | 33 |

I scanned all **34 prong/facade files** using exact Git blobs, masked nested comments/strings, and mapped every lexical `sorry`/`admit` to its full theorem namespace. There are 33 standalone `sorry` proof bodies in **19 files**, and no unmatched or non-theorem admission. Generated/admitted-dependent corollaries are not additional direct targets.

Every owner file itself is outside the role manifest. Nevertheless every complete local import closure intersects it. The closure union contains **235 source files**, including **59 CONSUMER + 116 PROVIDER_ONLY = 175 distinct blocking paths**. There are no unresolved TCSlib imports, no local import cycles, and no CHECK_ONLY aggregate in any candidate closure. Each closure includes its owner.

| Candidate owner | Targets | Local closure | Consumer intersections | Provider-only intersections |
|---|---:|---:|---:|---:|
| `Authentication/DLHash.lean` | 1 | 89 | 27 | 58 |
| `Authentication/HashAndSign.lean` | 1 | 92 | 29 | 58 |
| `Authentication/Lamport.lean` | 1 | 90 | 28 | 58 |
| `Authentication/PRFMAC.lean` | 1 | 113 | 44 | 65 |
| `Composability/CCA2Scheme.lean` | 1 | 113 | 44 | 65 |
| `Composability/NonMalleable.lean` | 1 | 118 | 44 | 69 |
| `Composability/PRFScheme.lean` | 3 | 115 | 46 | 65 |
| `Composability/PublicKey.lean` | 1 | 117 | 44 | 69 |
| `Composability/SequentialZK.lean` | 5 | 60 | 17 | 42 |
| `Composability/SimNonMalleable.lean` | 2 | 119 | 44 | 69 |
| `Randomness/Derandomization.lean` | 1 | 143 | 21 | 94 |
| `Randomness/Extraction.lean` | 1 | 30 | 7 | 22 |
| `Randomness/Learning.lean` | 1 | 110 | 42 | 63 |
| `SecureComputation/ComposeSecurity.lean` | 3 | 32 | 7 | 20 |
| `SecureComputation/Garbling.lean` | 1 | 3 | 0 | 2 |
| `SecureComputation/GarblingSecurity.lean` | 1 | 111 | 43 | 63 |
| `SecureComputation/ObliviousTransfer.lean` | 2 | 66 | 22 | 42 |
| `SecureComputation/SpecialEncryptionSecurity.lean` | 3 | 108 | 43 | 63 |
| `SecureComputation/Yao.lean` | 3 | 122 | 44 | 69 |

The smallest closure is exactly `SecureComputation/Garbling.lean`, `Complexity/CircuitComplexity/DAGCircuit.lean`, and `Cryptography/Foundations/Probability.lean`. Both imported owners are **PROVIDER_ONLY**. Thus `uprob_not_good_le` is excluded even though neither provider needed to appear among the 122 delivered changed paths.

`candidate-intersections.json` records all 33 full declaration names, line ranges, source/declaration hashes, every complete closure path, every intersecting role path and a shortest import chain to each blocker. `source-inventory.json` and `source-paths-sha256.tsv` give path, SHA-256, Git blob identity and byte count for all **1,108 TCSlib library sources plus two audit modules**; import edges include external package boundaries. `lexical-target-inventory.json` includes the zero-admission files. The independently authored `screen_dependencies.py` reproduces the screen with `python3 -I` using read-only Git.

This is a conservative source-import screen, not a proof-completion, native replay, semantic declaration-dependency or package audit. It deliberately does not waive a file merely because a proposed proof might avoid its changed declaration. Mutable working-tree source, the cleanup delivery's 122-path actual diff, worker scripts and native objects were not inputs. No library/Main/exchange edits, Git mutations, Lean/cache/build/app calls or proof attempts occurred. Nothing should be forced into a new helper or primitive to create artificial eligible work.

**Not yet clear to merge — this screen authorizes no new proof target; Gate06 audit-comment dispositions and existing-source checks remain separate work.**
