# GI attemptAt_poly: one-proof public-reader repair proposal

**Unapplied, unchecked proposal.** Explicit Gate06 worktree:
`/Users/seyoonr/.codex/worktrees/ps-gate06-integration/tcslib-pass-shelat-ch2-4`.
All source input was read using exact `git show e9d64158461bfe24ddc88ab885bc4017899b4c16:<path>`. No mutable source file supplied an input.

## Scope and composition

Only the existing `GIZK.attemptAt_poly` proof declaration and its sketch are repaired. Six missing canonical owner equations are added as **term rfl** readers:

- `ZeroKnowledge/Encoding.lean`: `decGraph_eq` (the complete total-decoder equation) and `decGraph_fst`.
- Global `ZeroKnowledge/GraphIsomorphism.lean`: `instanceVertexCount_eq`, `instanceG₀_eq`, `instanceG₁_eq`, `samplePerm_eq`.

These are the **global** helpers used by GIZK, not the GI.Proofs shadow definitions. No Interaction reader is added: existing efficiency/uniformity/view/history readers suffice. No host/helper definition, simp attribute, premise, admission, algorithm, import or option changes.

The four earlier GI owner proposals were composed strictly in memory; their combined Proofs SHA-256 is `bcf23cb653f839477a26b3961ab71f8b4000c7b50cc8ff820889ccf275b418af`. This new patch has separate hunks in the three files below and does not overwrite or modify those proposals or the completed inherited review.

**Encoding is a newly touched owner module beyond the initial 51-module survey.** Root has authorized this routine API addition and must include it in the dynamic post-repair scope, collector and affected replay; the initial survey list is not the final scope.

## First logged failure and latent reads

Completed evidence:
`/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4/briefs/pass-shelat-ch5-8/maintainer/gate06-integration-2026-11-06/evidence-rule10-r2/runs-v3/G06Seal_046_TCSlib_Cryptography_ZeroKnowledge_GraphIsomorphismZK_Simulator_HarnessV3.log`.

The first selected error is **source257:9 → probe307:9**, log line **1070**: destructuring `hV' : V'.Efficient` fails because the foreign predicate is sealed. The proof stops there, so later apparent conversions require static review.

| Frozen proof site | Read/conversion | Proposed public route |
|---|---|---|
| 257 | Destructure `Strategy.Efficient` | `(Strategy.efficient_iff V').mp hV'` |
| 273–275 (`hc`) | Treat foreign `coinBlock` as drop/take | Pointwise `ptc_congr` with `coinBlock_eq` |
| 305–306 (`hn`) | Treat global `instanceVertexCount` as square-root length | Pointwise `congrArg` with owner `instanceVertexCount_eq` |
| 308–315 (`hπ`) | Sampler body and decoded count | Owner `samplePerm_eq`, `instanceVertexCount_eq`, canonical `decGraph_fst` |
| 322–333 (`hH`) | Global `instanceG₀/G₁` bodies | Owner `instanceG₀_eq/instanceG₁_eq`, preserving existing branch split and decoder/sampler operations |
| 348 (`hadv`) | Read `A.Uniform` as advice clauses | `fun k => hA.advice_eq k` |
| 350–351 (`hmsg`) | Singleton history encoding after run/layout readers | Existing `Strategy.encodeMsgs_cons/nil` equations |
| 368–381 (`hview`) | View encoding and its two-message history | Term chain from `View.encode_mk`, two `encodeMsgs_cons` equations and `encodeMsgs_nil` |

The permutation witness theorem is a public explicit lambda over `(decGraph word).1`; there is no opaque `encPermFromCoins` function needing another reader. Reading its count through canonical `decGraph_fst` aligns it with `samplePerm` and avoids using the legacy GIZK decoder proof as a new conversion step.

The final `attemptAt/attemptStr` lists contain only **same-file definitions**, so they remain legal owner-local reductions. Existing layout/count/scan facts are applied through their published statements. The bare simplification steps assembling elementary pair/Boolean expressions remain unchanged; no explicit foreign definition is added to a tactic list.

Log SHA-256: `16c93aebe5cad1e0d7a6af047d2e86dca59f9681b1367a32decfff4bfa3b405b`.

## Canonical owner equations and algorithm preservation

`decGraph_eq` exposes the exact total decoder: `⟨sqrt |w|, fun u v => w.getD (finProdFinEquiv (u,v)) false⟩`. Its first-projection equation is proved in the decoder's actual owner. Both hold for arbitrary words; no square-length or well-formedness condition is added.

The four global graph/sampler equations reproduce the original formulas exactly. They retain the same decoded vertex count, graph words, campaign `permBits/permTrials`, coin table and identity fallback. The sampler and graph algorithms remain literal source matches.

Within `attemptAt_poly`, all runtime functions, bounds, block cuts, success condition and view contents are preserved. The new `hc`/`hn` wrappers and history/view congruences change only the proof route. Existing local tactic blocks are reused, and the view equation is a term chain; **no tactic block is added**. The theorem's complete header was compared literally through `:=`.

## Source fingerprints and line budget

| Source | Frozen SHA-256 | Proposed SHA-256 | Physical lines |
|---|---|---|---:|
| `TCSlib/Cryptography/ZeroKnowledge/Encoding.lean` | `ee5b3a7fc84e24346c0a71a99b1b724746d8c653e986b866cde4b4f9e0177db7` | `a2a354fd0a89b117022922f416b431a26393b207dbf65e72c4f9a6e3c4247ddc` | 690 → 698 |
| `TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean` | `5f2ee6a12b26e8864c55d5e0bf592cc234fdae1e5741d5e98ca03ae4ddc07002` | `c37dd3e13e4cd00afa895e9dd78d193f4dee2e59f8913add41d025f37f861302` | 989 → 999 |
| `TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK/Simulator.lean` | `0182277d6102dd8ade31fcd24770a3a9f7f0ac9c807fa201c3a58f468dadfe38` | `52814b1b7d7d0a1ce7e2e23965d02faadb019a2c7c65478e25c0695079281ea7` | 464 → 473 |

Patch SHA-256: `4bbb6c2c335ab64d700fb121b740b946703cbd879e9c1833ced18c8aea74328e`.

The global GraphIsomorphism file remains within the policy cap: 999 physical lines, or **1000** using the style script's final-empty-line convention. Its small owner reading equations are kept adjacent to their definitions without extra blank lines. Root must retain that line-budget check when composing later edits; no new size exception is claimed.

All old definition bodies in the two owner files were checked literally retained, and `attemptStr`, `attemptAt`, `sim` remain literal source matches in Simulator. Every source file's `:= by` count is unchanged. The new reader text introduces neither `@[simp]` nor admissions.

## Native checks and limits

Root should check Encoding first, then its affected dependency closure, the prior Proofs stages, the global GraphIsomorphism owner and Simulator in valid import order. Rebuild imported objects before testing reader-dependent consumers. The dynamic post-repair module list must include Encoding.

Then native-check the entire selected proof, its ordinary axiom set, collected reads and explicit lists, and rerun the valid seal. In particular the `hview` reader/congruence term's inferred fields must elaborate; no native elaboration is claimed here.

The other four original Simulator source diagnostics remain untouched inherited observations: `decGraphAt_padSq`, local `decGraph_eq_of_sqrt`, `sim_poly`, `exists_simulator`. Existing helper proofs outside `attemptAt_poly` are not repaired or declared passing. This proposal covers the final one of the seven genuinely changed GI roots, not every legacy failure in its dependency closure.

No Lean/cache, apps, library edits, Git mutations or received-program execution occurred. Only separate ignored patch/notes artifacts were saved.

**Not yet clear to merge — the six owner terms and one proof repair are unapplied/unchecked and require root's serial replay/seal.**
