# Final repair source-review reconciliation

**Static verdict remains 0 blockers / 0 majors / 0 minors.** This append-only addendum reconciles the delivered review to final HEAD `3f6db40e1688c4a0bb922c9575dd3bd2157a650b`, campaign base `eee107e92a7db11f1f8c98a5c2867304f57ddc54`. All earlier review artifacts remain unchanged. No Lean/cache/native check was run by this reviewer.

At 2026-11-07T12:45:24.201673+00:00, all **1,108** current library source files, including the root `TCSlib.lean` facade, were byte-identical to this HEAD's Git archive. Exact paths and SHA256 values are in `final-repair-source-review.final.sha256` (SHA256 `549c7071cfc76b377738fa7914eaa2bc998104dcdde25c36455d1363736d020a`). The source set and all bytes were reread before publishing this addendum.

Exactly two files differ from the delivered `final-repair-source-review.current.sha256`:

| Source | Final SHA256 | Reviewed overlay |
|---|---|---|
| `TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK/Simulator.lean` | `43e183a6d4e106fa5d720a0f3f34771b1d891fa7174d9d295b02da6e0e078d7e` | One existing `attemptAt_poly.hπ` subproof |
| `TCSlib/Cryptography/Randomness/Learning.lean` | `2243c82c7f547ac2406c5c29edc765c86920659238214f73f757932c96c3ae0b` | Existing theorem's English labelled proof sketch only |

Simulator's `hcount` obtains the decoded graph's vertex count through published `decGraph_eq` and `instanceVertexCount_eq`. Congruence transports the complete list-valued expression `k ↦ encPerm (samplePerm k tape)`, so the dependent permutation index and sampler parameters move together. Published `samplePerm_eq` supplies the sampler equation; the final `.symm` gives the orientation required by the existing `ptc_congr`. Coin drop/take cuts remain exact. These total equations cover empty or malformed graph words and vertex count zero. A byte comparison against the committed initial review snapshot confirms that only the existing `hπ` proof body changed, with its header and all surrounding code preserved.

Learning's added sketch correctly describes the existing two-cutoff argument: negligible prediction advantage gives the eventual `1/n` bound, the positive gap `γ - δ` gives the second cutoff, and the existing PAC bound excludes weak learning. All bytes outside that one docstring are identical to the committed initial review snapshot.

Neither overlay changes a definition, public theorem header, data field, algorithm, security notion, premise, admission, helper definition or simp attribute. Simulator's new explicit lists still name only published equation lemmas (`Function.comp_apply`, `pairFstD_pairEncode`, `pairSndD_pairEncode`); the count/sampler readers are used as public theorem terms. The earlier repair-delta statement/data/decoder/policy conclusions remain applicable.

Root reported Simulator R6 with the same four inherited diagnostics and the changed site repaired; native affected replay and final Learning/downstream reconciliation were still in progress. These reports are context only, not independently certified by this reviewer. Fresh final source-matched replay, collection/seals/controls, axiom comparison and failure reconciliation remain root's separate work.

Only read-only source/Git inspection and ignored review-artifact writes were performed. No received tool, native command, Lean/cache process, computer app, library edit, Git mutation or campaign-evidence write occurred.
