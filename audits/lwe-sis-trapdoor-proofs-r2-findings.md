# Gate 12 round 2 findings

**PASS for the 40-fill proof gate.** Zero blockers, zero majors, zero minors. F01 and F02 are resolved. Four continuing notes remain open.

## Audited pins

| Item | Revision |
|---|---|
| Exchange `exchange/pass-shelat-ch5-8` | `3d1d76833cf36a614559338dd31a2dc0459618d5` |
| Repaired Lean and root | `93dc88648f117877e42aaf58ba7b911c76a4b63a` |
| Bundled records | `b529e9cd722d5116ce850c32202efaaa0b109854` |
| Round 1 exchange, Lean, and records | `7200aafd9ae628aeef6a7aad69f2125618b903433` · `3bf1cb424b10abef3ae7a438c6b7d0e1916d0800` · `aff0a82679c201834415cbe293393fef7477f6e7` |
| Gate 11 baseline and statement freeze | `259ff8a13ba08034a15ab7c8464d5ad4a122d6fd` · `17b2a282b545c6ebca3fccc88d518d18ae78f485` |
| Approved F01 patch and F02 documentation commit | `089c8dacf161a475ffff85b1b108b11529bd094c` · `d3bb52db5aaf249a35e83506371a3c86e76cb69a` |
| Draft #250 head and live target `cryptography/lwe-sis-constructions` | `dc016b42dde7569518d4c1fb293c122f92e99c77` · `41aaf0a1acf29318fa8d741dadd9f5f585e43c93` |
| #255 reader source and landing records | `004bd5b89e48dec52e045bba32439375b82eaead` · `6410ad6375afe46dcea23b882dcf7eab302fe78e` |

I resolved `<EXCHANGE_COMMIT>` to the publication commit for the packet matching the supplied SHA-256 `f0422ea44c6ab0b737e62f24e3dcf3c02e693f35e03772e32efba15a12f78829` and **5,652,216 bytes**. The outer and nested `SHA256SUMS` pass. Both ordered indexes agree, and all **260** section payloads match their revision-qualified Git blobs. [Gate packet](https://github.com/Shilun-Allan-Li/tcslib/tree/3d1d76833cf36a614559338dd31a2dc0459618d5/lwe-sis-constructions/outbox/gates/12-sis-trapdoor-proofs-r2) · [Draft #250](https://github.com/Shilun-Allan-Li/tcslib/pull/250)

## Round 1 findings

**F01 · Resolved.** The committed diff matches the approved patch byte for byte. `LWE.binaryErrorSum_bound` now owns the proof. The integer triangle inequality bounds the masked sum by the sum of magnitudes. A false bit contributes zero and a true bit contributes at most the common bound. Counting all positions gives

$$
\left|\sum_i e_i r_i\right| \le \sum_i |e_i r_i| \le \sum_i B = mB.
$$

The empty sum is included. The theorem needs only the sample count and coordinatewise integer bounds. Its docstring identifies the deterministic bounded-support specialization of Pei16 §5.2.1. The direct Mathlib import supplies `Finset.le_sum_of_subadditive`. `Regev.subsetError_bound` passes the original error vector and coins. `Lossy.error_sum_bound` imports the owner and passes the selected error column and original input bits. Both frozen signatures and their uses in `decrypt_encrypt` and `lossy_range_card` are preserved. [Approved patch](https://github.com/Shilun-Allan-Li/tcslib/commit/089c8dacf161a475ffff85b1b108b11529bd094c) · [Shared theorem](https://github.com/Shilun-Allan-Li/tcslib/blob/93dc88648f117877e42aaf58ba7b911c76a4b63a/TCSlib/Cryptography/LWE/Basic.lean#L73) · [Pei16 §5.2.1](https://web.eecs.umich.edu/~cpeikert/pubs/lattice-survey.pdf#page=37)

**F02 · Resolved.** The separate commit changes only comments. `Lossy.Matrix` now cites pp. 33–37, covering the image count, and points to the proved finite column hybrids in `Lossy.Experiments`. `AllButOne.Basic` now cites pp. 37–39, covering branch evaluation, designated cancellation, and the image argument. [Documentation diff](https://github.com/Shilun-Allan-Li/tcslib/commit/d3bb52db5aaf249a35e83506371a3c86e76cb69a) · [PW10](https://sites.cc.gatech.edu/fac/cpeikert/pubs/lossy_tdf.pdf#page=33)

## Encoding and SIS · 24 fills

| Module | Fills | Checked |
|---|---:|---|
| `Encoding.BooleanVector` | 5 | The step retains its width context and composes total leaf machines. Pair-length bounds apply to malformed framing. Each round appends one block and reads the same defaulted bit as `padFin`, including truncation and zero width. |
| `Encoding.DyadicLinearAlgebra` | 10 | Both step bounds use total projections. The dot loop starts at a width-sized zero and maintains the canonical modular sum. The outer loop retains the input vector and cuts exact row-major blocks. Widths are unconditional, including zero rows, columns, or width. |
| `Hashing.SIS.CollisionOutput` | 7 | The streams read positions `i` and `m+i` with false defaults. Sign and xor magnitude agree with the encoder at every width, and positive width gives exact decoding. A padded collision gives a nonzero kernel difference with at most one unit of squared norm per column. The probability inclusion keeps the original matrix and finder coins. |
| `Hashing.SIS.Implementation` | 2 | Output width holds for all raw inputs. A canonical matrix is multiplied by exactly the padded domain bits. |

## Finite trapdoors · 16 fills

| Module | Fills | Checked |
|---|---:|---|
| `Lossy.Gadget` | 4 | Scaling preserves residue congruence and is additive. The half-step shift puts either signed error in the rounding interval and the wraparound quotient vanishes in the small modulus. Digit injectivity uses the existing block equivalence. |
| `Lossy.Matrix` | 4 | The retained secret product cancels, leaving the original signed error sums. The image factors through the first modular product and one integer interval per column, giving the bound $q^d(2NB+1)^w$. The bit-loss theorem uses the supplied numeric budget. |
| `Lossy.Experiments` | 4 | The seed bijections retain the public matrix and test coins. A real secret and its noise seeds update one column in the next hybrid, and an ideal value vector updates that column in the preceding hybrid. Endpoint marginalization and telescoping cover zero columns. Both fixed shifts preserve the same uniform ideal. |
| `AllButOne.AntiCyclic` | 2 | Wrapped indices have the prescribed sign, and subtraction commutes with the construction. The branch coefficients have magnitude at most one, giving a digit-product bound strictly below half the message modulus. |
| `AllButOne.Basic` | 2 | The designated branch restores exactly the subtracted gadget and inherits the image bound for the original concealed matrix and errors. |

## Freeze and execution

- Four library paths changed from round 1. The other **149 of 153** pinned files match byte for byte. Only the two wrapper bodies changed, and the shared theorem is the sole new declaration. The Gate 11 comparison identifies exactly 40 filled admissions. Of those 40 bodies, 39 are identical to round 1.
- I reran the seven-facade closure of **144 modules** and both probes serially with Lean 4.25.0, using pinned dependency objects and a fresh TCSlib object tree. All 144 module logs and the axiom log match the round 2 bundle byte for byte. The type log matches the round 2 hash and the round 1 bytes, including all **220** universe and type fingerprints. Style lint reproduces **0 failures and 2 inherited warnings over 41 files**.
- The **309** axiom prints cover 220 frozen declarations, 88 backing contracts, and the new theorem. All **609** retained owned constants keep their identities and exact axiom sets. The sole addition brings the inventory to **610**, with zero compiler auxiliary changes. All 40 fills and the shared theorem use subsets of `propext`, `Quot.sound`, and `Classical.choice`. The **18** owned `sorryAx` entries match the exact source stubs and warning declarations. The **17** inherited admission warnings are separate. Of the 144 module logs, 143 match round 1 byte for byte. Only warning locations moved in `Lossy.Matrix`. [Round 2 evidence](https://github.com/Shilun-Allan-Li/tcslib/tree/b529e9cd722d5116ce850c32202efaaa0b109854/briefs/lwe-sis-constructions/fills/07-sis-trapdoor/round2/evidence)

## Continuing notes

- **N01.** The 18 admissions comprise nine counted-loop consumers, seven positional-reader and gadget obligations, and two anti-cyclic rank obligations. The registry and head-envelope disposition and `Randomized.blockVal_eq` are pending. `Cyclotomic.Roots` is outside the scoped cache. [Exact inventory](https://github.com/Shilun-Allan-Li/tcslib/blob/b529e9cd722d5116ce850c32202efaaa0b109854/briefs/lwe-sis-constructions/fills/07-sis-trapdoor/round2/evidence/freeze.json#L23) · [Coordination](https://github.com/Shilun-Allan-Li/tcslib/blob/b529e9cd722d5116ce850c32202efaaa0b109854/briefs/lwe-sis-constructions/gates/08-construction-statements/COORDINATION.md)
- **N02.** The 44-page PW10 author PDF matches SHA-256 `74f48b0eff6f4a0afd52ffe2bfddc6bef006c241c458812bfe085ce85059752c`, and the layout hashes reproduce for all seven pages. The finite proofs use exact dyadic scaling and deterministic entrywise bounds. Scoped ingestion and approved matching remain open. [Source manifest](https://github.com/Shilun-Allan-Li/tcslib/blob/b529e9cd722d5116ce850c32202efaaa0b109854/briefs/lwe-sis-constructions/fills/07-sis-trapdoor/pw10-primary-source.json)
- **N03.** Efficient samplers and schedules, asymptotic primitive and game bridges, other-branch inversion, strong one-time signatures, and CCA2 remain separate. SIS hardness is an independent assumption.
- **N04.** Both audited #255 reader blobs match the merged target and the draft. I reproduced merge tree `79ea2632d6879cb22b51660ea972ff7ff84bdf0f` for the repaired pin and verified the live #250 merge ref `d7a5e7bc2f3ccb6d83c29bd445702f50c4a76c68`. Both match the repaired Lean tree, including the root and five facade export paths, and the build pins. Repeat the exact-target and export checks at landing. [#255](https://github.com/Shilun-Allan-Li/tcslib/pull/255) · [Preview receipt](https://github.com/Shilun-Allan-Li/tcslib/blob/b529e9cd722d5116ce850c32202efaaa0b109854/briefs/lwe-sis-constructions/fills/07-sis-trapdoor/round2/evidence/integration-preview.json)

**Notation.** In the subset-sum bound, $i$ indexes the $m$ positions, $e_i$ is a signed integer error, $r_i\in\{0,1\}$ is its selection bit, and $B$ bounds each $|e_i|$. In the SIS row, `i` indexes the columns and `m` is the column count. In the image bound, $q$ is the modulus, $d$ the secret dimension, $N$ the input length, $B$ the entrywise error bound, and $w$ the number of concealed columns.
