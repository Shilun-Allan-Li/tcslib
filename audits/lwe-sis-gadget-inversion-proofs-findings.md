# Gate 13 round 1 findings

**PASS** for the nine proof fills and approved shared reader in draft PR #250 of `Shilun-Allan-Li/tcslib`. **0 blockers, 0 majors, 0 minors, 4 continuing notes.** [Draft #250](https://github.com/Shilun-Allan-Li/tcslib/pull/250)

## Audited pins

| Item | Exact revision or value |
|---|---|
| Exchange `exchange/pass-shelat-ch5-8` | `4cd97c861b80fb7d3ea7f40a772657c7aad367eb` |
| Lean and root | `713093c36ac66f7e56e9354581f0bb3f59772341` |
| Bundled records and draft head | `f4b1e343061101565e9ac93b517d93fec6c4ded3` |
| Gate 12 round 2 passed Lean and root | `93dc88648f117877e42aaf58ba7b911c76a4b63a` |
| Gate 12 passed intake | `ce421a2f5e4abf50b776c190a95788ce926494f0` |
| Rank Lean and root | `75a4214dc098cd6c363d00c34f569bac23eb4555` |
| Rank records and current-wave baseline | `d34b0e409bc179167921073a731a0eb3e009f267` |
| Approved reader | `2414fd3eae05c99474d1888609b01ac5989523a5` |
| Central target `cryptography/lwe-sis-constructions` | `41aaf0a1acf29318fa8d741dadd9f5f585e43c93` |
| Lean and Mathlib | `leanprover/lean4:v4.25.0` · `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e` |
| Bundle SHA-256 | `fabbecce1b5e1c68872a37487f18ad334c8bd75065241028b2afa85a4a54a52f` |
| Bundle size and sections | 5,563,811 bytes · 247 sections (153 source, 94 records) |

All five exchange checksums and 56 nested evidence checksums passed. The two ordered indexes agree on revision, path, length, and digest. Every extracted section matches its pinned Git blob, including the first-section pack. [Exchange packet](https://github.com/Shilun-Allan-Li/tcslib/tree/4cd97c861b80fb7d3ea7f40a772657c7aad367eb/lwe-sis-constructions/outbox/gates/13-gadget-inversion-proofs-r1)

## Source freeze and proof review

The Lean diff from the passed Gate 12 snapshot is confined to five files. The other 148 indexed source paths, the root exports, and the build pins match byte for byte. The two rank bodies and seven consumer bodies replace exactly nine `sorry` stubs with their signatures preserved. Rank adds the disclosed `AdjoinRoot` and `Cyclotomic.Roots` imports. I independently enumerated the 220 frozen declarations across 19 modules. [Rank commit](https://github.com/Shilun-Allan-Li/tcslib/commit/75a4214dc098cd6c363d00c34f569bac23eb4555) · [Consumer commit](https://github.com/Shilun-Allan-Li/tcslib/commit/713093c36ac66f7e56e9354581f0bb3f59772341)

Applying the approved four-line patch to the exact parent reproduces `RandomBits.lean` at the isolated reader commit and the final pin. `Randomized.blockVal_eq` is a complete non-simp equation, by `rfl`, for `bitsVal` of the width-`b` slice at offset `i*b`. It has an empty axiom set. [Reader commit](https://github.com/Shilun-Allan-Li/tcslib/commit/2414fd3eae05c99474d1888609b01ac5989523a5)

| Checked fills | Finding |
|---|---|
| `AllButOne.antiCyclic_mulVec_injective`, `branch_difference_injective` | The quotient by the rational cyclotomic polynomial of order `2^(u+1)` gives the power basis for width `2^u`. A wrapped column index picks up the minus sign from the width-th power of the root. Reindexing the row sum identifies the transpose action with field multiplication. The power basis detects nonzero integer coefficients and lets cancellation recover each coefficient. At `u=0` the polynomial is `X+1` and the single row needs no wrap. Distinct Boolean branches give a nonzero integer difference. [Rank proofs](https://github.com/Shilun-Allan-Li/tcslib/blob/713093c36ac66f7e56e9354581f0bb3f59772341/TCSlib/Cryptography/TrapdoorFunctions/AllButOne/AntiCyclic.lean#L70) |
| `Lossy.digits_val`, `gadget_mulVec` | The slice has length `b`. Its position `k` is row-major index `j*b+k`. Reindexing the existing little-endian sum gives the exact digit, and the gadget transpose retains exactly the matching block. For `b=0` the sum is empty and the digit is zero. At `w=0` there is no digit coordinate. [Gadget proofs](https://github.com/Shilun-Allan-Li/tcslib/blob/713093c36ac66f7e56e9354581f0bb3f59772341/TCSlib/Cryptography/TrapdoorFunctions/Lossy/Gadget.lean#L183) |
| `Lossy.residual_injectiveKey`, `recover_evaluate`, `evaluate_injective` | `residual_conceal` removes the secret product. `encode_intCast` commutes the exact scale through the gadget product and leaves the original signed error sum. Its magnitude is at most `w*b*B`. Strict separation `2*(w*b*B) < 2^a` permits `decode_encode_add`, and the inverse block equivalence gives a left inverse for every input. This also covers an empty secret dimension. [Recovery proofs](https://github.com/Shilun-Allan-Li/tcslib/blob/713093c36ac66f7e56e9354581f0bb3f59772341/TCSlib/Cryptography/TrapdoorFunctions/Lossy/Matrix.lean#L143) |
| `AllButOne.residual_branch`, `evaluateBranch_injective` | After cancellation, the queried shift minus the designated shift gives the encoded integer branch-difference product plus the original error sum. The same strict rounding check recovers the product residue. Each signed coordinate has magnitude at most `2^u*(2^b-1) < 2^(b+u)`. Equality of residues makes the difference a multiple of `2^(b+u+1)`, and the triangle inequality makes its magnitude strictly smaller than that modulus. The integer products are equal, so rank and digit injectivity give equality of inputs. [Branch proofs](https://github.com/Shilun-Allan-Li/tcslib/blob/713093c36ac66f7e56e9354581f0bb3f59772341/TCSlib/Cryptography/TrapdoorFunctions/AllButOne/Basic.lean#L119) |

The sketches track the implemented arguments. The fills use the public readers and reuse the concealed residual and shared binary error-sum bound. Gate 12 findings F01 and F02 remain resolved. [Gate 12 disposition](https://github.com/Shilun-Allan-Li/tcslib/blob/f4b1e343061101565e9ac93b517d93fec6c4ded3/audits/lwe-sis-trapdoor-proofs-resolutions.md)

## Execution and axiom evidence

I independently replayed the exact seven-facade closure on x86-64 Linux with Lean 4.25.0 and the pinned Mathlib cache. All 144 modules produced fresh objects with zero errors and byte-identical logs. The logs contain nine owned and 17 inherited admission warnings. Compared with Gate 12, 140 module logs are byte-identical and every non-admission warning is preserved. Style reproduced zero failures and two inherited warnings over 41 files. All 178 recorded rank dependency source, archive, and object fingerprints also matched.

The independent axiom probe reproduced the log byte for byte. The 329 explicit prints and 616-constant inventory reconcile with Gate 12. All nine fills depend only on `propext`, `Quot.sound`, and `Classical.choice`. The additions are the reader and five compiler auxiliaries. `Lossy.evaluate.congr_simp` moves from `AllButOne.Basic` to `Lossy.Matrix` with the same name, kind, visibility, and axiom set. The nine owned `sorryAx` entries are exactly the remaining source stubs. [Gate 13 evidence](https://github.com/Shilun-Allan-Li/tcslib/tree/f4b1e343061101565e9ac93b517d93fec6c4ded3/briefs/lwe-sis-constructions/fills/09-gadget-inversion/evidence)

I replayed the type probe at all three pins, rebuilding the affected closures of 12 modules for rank and four for Gate 12. All 220 Gate 13 universe and type representations match rank exactly. Of these, 216 also match Gate 12 exactly. The four differences are integer ring projections in `antiCyclic_mulVec_injective`, `branch_difference_injective`, `branch_message_bound`, and `residual_branch`. Their before and after fingerprints reproduced, and independently regenerated reflexivity certificates passed the kernel with the recorded log hash. [Type evidence](https://github.com/Shilun-Allan-Li/tcslib/blob/f4b1e343061101565e9ac93b517d93fec6c4ded3/briefs/lwe-sis-constructions/fills/09-gadget-inversion/evidence/type-checks.json)

## Continuing notes

- **N01.** Seven counted-loop or dependent efficiency obligations and two asymptotic SIS CRH obligations remain. The public `forLoop` registry and head-envelope disposition remain separate. The 17 inherited admission warnings are tracked separately. [Admission inventory](https://github.com/Shilun-Allan-Li/tcslib/blob/f4b1e343061101565e9ac93b517d93fec6c4ded3/briefs/lwe-sis-constructions/fills/09-gadget-inversion/evidence/axiom-delta.json)
- **N02.** The exact 44-page PW10 author PDF and all seven consumed page layout hashes reproduced. Sections 6.3.2–6.4 support the transposed gadget and rank arguments. The formalization explicitly specializes to exact dyadic scaling and deterministic bounded errors. Scoped ingestion and approved matching remain open. [PW10, pp. 35–39](https://web.eecs.umich.edu/~cpeikert/pubs/lossy_tdf.pdf#page=35)
- **N03.** The finite all-but-one theorem proves injectivity. Efficient other-branch recovery, family-level sampler and security bridges, strong one-time signatures, and CCA2 remain separate. SIS hardness remains independent.
- **N04.** The reproduced merge preview tree `997489939120a1c1f5221a3a9780671beedf23f7` and live #250 merge ref `2a58170bc9af788e71e4047a0395f17e021aeedf` preserve the audited library, root exports, and build pins. Both #255 reader blobs match the merged target. Whole-library elaboration and exact-target export checks remain landing checks. [Merge preview receipt](https://github.com/Shilun-Allan-Li/tcslib/blob/f4b1e343061101565e9ac93b517d93fec6c4ded3/briefs/lwe-sis-constructions/fills/09-gadget-inversion/evidence/integration-preview.json)

**Notation.** `b` is bits per digit, `w` is block count, `u` is the base-2 log of the branch width, `a` is the scale exponent, `B` bounds each integer error, `X` is the polynomial indeterminate, and `i`, `j`, and `k` are block or bit indices as used in the declarations.
