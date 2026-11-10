# Gate 12 · SIS encoding and finite trapdoor proofs

**Verdict · HOLD on policy.** All 40 fills pass the mathematical and axiom checks. **0 blockers, 1 major, 1 minor, 4 continuing notes.**

## Audited pins

| Item | Revision |
|---|---|
| Exchange `exchange/pass-shelat-ch5-8` | `7200aafd9ae628aeef6a7dd69f2125618b903433` |
| Filled Lean and root | `3bf1cb424b10abef3ae7a438c6b7d0e1916d0800` |
| Bundled records | `aff0a82679c201834415cbe293393fef7477f6e7` |
| Original statement freeze | `17b2a282b545c6ebca3fccc88d518d18ae78f485` |
| Gate 11 proof baseline | `259ff8a13ba08034a15ab7c8464d5ad4a122d6fd` |
| PR #250 target `cryptography/lwe-sis-constructions` | `27f9ea89b72d84abaec8128f2abd826f24aaced4` |
| PR #255 reader source and landing records | `004bd5b89e48dec52e045bba32439375b82eaead` and `6410ad6375afe46dcea23b882dcf7eab302fe78e` |

The bundle is **5,020,677 bytes** with SHA-256 `49b4ed235b2213d205410f320799cf4e317556ef404e6067ea1d04d5862a12a1`. The outer and nested `SHA256SUMS` pass. Both ordered indexes agree and all 236 section payloads match the Git blobs at their listed revisions. Draft #250’s publication head `0f1f10b16c1fb674995ebbfd1292f10a008597bc` has the same library source, root and build pins as the filled revision. [Gate packet](https://github.com/Shilun-Allan-Li/tcslib/tree/7200aafd9ae628aeef6a7dd69f2125618b903433/lwe-sis-constructions/outbox/gates/12-sis-trapdoor-proofs-r1) · [Draft PR #250](https://github.com/Shilun-Allan-Li/tcslib/pull/250)

## Findings

**F01 · Major · Undisclosed duplicate bound.** `Lossy.error_sum_bound` reproves `Regev.subsetError_bound`. Set the existing theorem’s LWE parameters to `⟨0, N, 2, by decide⟩`, use `fun i => E i j` for its error vector and pass the original `x`, `B` and `fun i => hE i j`. Its conclusion is definitionally the exact goal. A separate Lean probe checked this instantiation. The fill report omits the duplication disposition required by `policy.md` §1 and `workflow.md` §4. Keep both frozen signatures and either reuse a shared bounded binary subset-sum lemma through an owner-reviewed change or record explicit maintainer acceptance with a deduplication owner and schedule. [New bound](https://github.com/Shilun-Allan-Li/tcslib/blob/3bf1cb424b10abef3ae7a438c6b7d0e1916d0800/TCSlib/Cryptography/TrapdoorFunctions/Lossy/Matrix.lean#L154) · [Existing bound](https://github.com/Shilun-Allan-Li/tcslib/blob/259ff8a13ba08034a15ab7c8464d5ad4a122d6fd/TCSlib/Cryptography/Encryption/PublicKey/Regev/Basic.lean#L136) · [Policy](https://github.com/Shilun-Allan-Li/tcslib/blob/3bf1cb424b10abef3ae7a438c6b7d0e1916d0800/policy.md#L124)

**F02 · Minor · PW10 anchors and overview.** `Lossy.Matrix`’s page range ends at 36, before the lossy count on p. 37. `AllButOne.Basic`’s ends at 38, before branch evaluation and the lossiness argument on p. 39. Extend the ranges and direct readers of `Lossy.Matrix` to the proved finite column hybrids in `Lossy.Experiments`. [Lossy overview](https://github.com/Shilun-Allan-Li/tcslib/blob/3bf1cb424b10abef3ae7a438c6b7d0e1916d0800/TCSlib/Cryptography/TrapdoorFunctions/Lossy/Matrix.lean#L23) · [All-but-one overview](https://github.com/Shilun-Allan-Li/tcslib/blob/3bf1cb424b10abef3ae7a438c6b7d0e1916d0800/TCSlib/Cryptography/TrapdoorFunctions/AllButOne/Basic.lean#L23)

## Encoding and SIS · 24 fills

| Module | Fills | Audit |
|---|---:|---|
| `Encoding.BooleanVector` | 5 | The step keeps its width context and composes the existing total bit and pairing machines. The length bound uses joint projection lengths on arbitrary framing. Each counted step adds exactly one width-sized block. The raw head/default at each position agrees with `padFin`, including truncation and zero width. [Source](https://github.com/Shilun-Allan-Li/tcslib/blob/3bf1cb424b10abef3ae7a438c6b7d0e1916d0800/TCSlib/Cryptography/Encoding/BooleanVector.lean#L62) |
| `Encoding.DyadicLinearAlgebra` | 10 | Both steps preserve their contexts and bound growth with total projections. The dot leaf composes scalar addition, multiplication and block cuts. The dot loop starts with a width-sized zero and maintains the canonical modular partial sum. The outer loop cuts exact row-major blocks, retains the vector and appends one dot result per row. The width proofs allow malformed pairs, empty dimensions and zero-width blocks. [Source](https://github.com/Shilun-Allan-Li/tcslib/blob/3bf1cb424b10abef3ae7a438c6b7d0e1916d0800/TCSlib/Cryptography/Encoding/DyadicLinearAlgebra.lean#L74) |
| `Hashing.SIS.CollisionOutput` | 7 | `take m` and `drop m` read positions `i` and `m+i` with false defaults, exactly the two padded halves. The step emits sign `!x && y` and xor magnitude with the unconditional sign-plus-width length. Encoder equality includes zero magnitude width. The exact decoder uses positive magnitude width and coordinate magnitude at most one. For the same matrix and original finder coins, distinct padded words with equal hashes give a nonzero kernel difference of squared norm at most the column count. The probability bound uses that pointwise inclusion under the stated norm budget. [Source](https://github.com/Shilun-Allan-Li/tcslib/blob/3bf1cb424b10abef3ae7a438c6b7d0e1916d0800/TCSlib/Cryptography/Hashing/SIS/CollisionOutput.lean#L89) |
| `Hashing.SIS.Implementation` | 2 | Output width is unconditional. With a canonical matrix, raw-word expansion feeds the canonical matrix product on the padded domain bits. [Source](https://github.com/Shilun-Allan-Li/tcslib/blob/3bf1cb424b10abef3ae7a438c6b7d0e1916d0800/TCSlib/Cryptography/Hashing/SIS/Implementation.lean#L58) |

## Finite trapdoors · 16 fills

| Module | Fills | Audit |
|---|---:|---|
| `Lossy.Gadget` | 4 | Scaling turns a change of representative by a multiple of $2^b$ into one by a multiple of $2^{b+a}$, giving integer-cast compatibility and additivity. For the perturbed residue $z$, its representative is $2^a m.\mathrm{val}+e+2^{b+a}t$. The strict error bound gives $0\le e+2^{a-1}<2^a$ for either sign. The rounded quotient is $m.\mathrm{val}+2^b t$, which casts back to $m$. Digit injectivity uses the existing block equivalence. [Source](https://github.com/Shilun-Allan-Li/tcslib/blob/3bf1cb424b10abef3ae7a438c6b7d0e1916d0800/TCSlib/Cryptography/TrapdoorFunctions/Lossy/Gadget.lean#L61) |
| `Lossy.Matrix` | 4 | Transposition and associativity cancel the retained $T(A^\top x)$, leaving the original signed integer error sum cast modulo $q$. Each error coordinate lies in $[-NB,NB]$. The output factors through the first modular product and these integer coordinates, giving $q^d(2NB+1)^w$ possible encodings of the factor. Multiplying the image bound by $2^k$ and applying the supplied budget bounds the resulting product by $2^N$. [Source](https://github.com/Shilun-Allan-Li/tcslib/blob/3bf1cb424b10abef3ae7a438c6b7d0e1916d0800/TCSlib/Cryptography/TrapdoorFunctions/Lossy/Matrix.lean#L120) |
| `Lossy.Experiments` | 4 | The column law reads one secret and independent original noise seeds for that column. The seed bijections retain the common public matrix and test coins. `uprob_update` absorbs a real secret/noise tuple into the next hybrid and an ideal value vector into the preceding one. The endpoints discard unused independent coins, including at zero columns. Telescoping gives the sum of gaps. Both fixed shifts translate the same uniform ideal bijectively, yielding two sums. [Source](https://github.com/Shilun-Allan-Li/tcslib/blob/3bf1cb424b10abef3ae7a438c6b7d0e1916d0800/TCSlib/Cryptography/TrapdoorFunctions/Lossy/Experiments.lean#L66) |
| `AllButOne.AntiCyclic` | 2 | Wrapped indexing negates exactly below the diagonal and distributes over subtraction. The branch difference entries have magnitude at most one, so the digit product is bounded by $2^u(2^b-1)<2^{b+u}$, below half the chosen message modulus. [Source](https://github.com/Shilun-Allan-Li/tcslib/blob/3bf1cb424b10abef3ae7a438c6b7d0e1916d0800/TCSlib/Cryptography/TrapdoorFunctions/AllButOne/AntiCyclic.lean#L46) |
| `AllButOne.Basic` | 2 | The designated branch adds back the exact matrix subtracted at key generation. The resulting map and its image bound use the original concealed matrix and original errors. [Source](https://github.com/Shilun-Allan-Li/tcslib/blob/3bf1cb424b10abef3ae7a438c6b7d0e1916d0800/TCSlib/Cryptography/TrapdoorFunctions/AllButOne/Basic.lean#L98) |

## Freeze and execution evidence

- The ordered census preserves **220 declarations in 19 modules**, including 57 definitions and 62 original `rfl` readers. Exactly 40 admission bodies change from Gate 11. The other 144 indexed source paths match byte for byte. The sole new import is `OneWayFunctions.Basic` in `Lossy.Experiments` for `uprob_update`, within the existing closure. Both #255 reader blobs match their audited pin. [Freeze record](https://github.com/Shilun-Allan-Li/tcslib/blob/aff0a82679c201834415cbe293393fef7477f6e7/briefs/lwe-sis-constructions/fills/07-sis-trapdoor/evidence/freeze.json)
- All 145 bundled log frames match their receipts. The serial sweep covers 144 modules in 382.262 seconds, followed by the 64.262-second probe. All 144 modules match the prior non-admission diagnostics, and 135 complete module logs match. The scoped style replay reproduced **0 failures and 2 inherited warnings over 41 files**. [Execution evidence](https://github.com/Shilun-Allan-Li/tcslib/tree/aff0a82679c201834415cbe293393fef7477f6e7/briefs/lwe-sis-constructions/fills/07-sis-trapdoor/evidence)
- The **308 axiom prints** comprise 220 source declarations and 88 backing contracts. The **609-constant** inventory grows by 16 compiler auxiliaries with zero changes of origin for existing constants. Of the 40 fills, 32 use `propext`, `Quot.sound` and `Classical.choice`, and eight use the first two. All backing contracts use standard axioms only. Exactly the 18 listed owned admissions use `sorryAx`.
- I independently replayed the 144-module closure at each revision with Lean 4.25.0. Each sweep ran serially in its own fresh object tree, with the two sweeps overlapping in wall time. The module logs and final 308-print, 609-constant axiom probe matched the bundled logs byte for byte. The two type probes were byte-identical and reproduced the recorded hashes and all 220 per-declaration universe and type fingerprints. The native scope covers the seven facades and their probes. The root export was compared at source.

The first cache request exceeded the campaign’s scoped bootstrap and hit a rate limit. The successful replay used the filtered restore of 2,335 pinned dependency objects.

## Continuing notes

**N01 · Remaining admissions.** The 18 source stubs, compiler warnings and `sorryAx` inventory agree exactly. The 17 inherited admission warnings are separate.

| Count | Obligations |
|---:|---|
| 7 | `polyTimeComputable_` contracts for `expandPoly`, `dotWords`, `dotPoly`, `matVecStep`, `matVecPoly`, `collisionOutputPoly`, `hashPoly` |
| 2 | `negligible_collisions_of_SIS`, `dyadic_collision_negligible` |
| 7 | `digits_val`, `gadget_mulVec`, `residual_injectiveKey`, `recover_evaluate`, `evaluate_injective`, `residual_branch`, `evaluateBranch_injective` |
| 2 | `antiCyclic_mulVec_injective`, `branch_difference_injective` |

The first nine stay on the counted-loop route pending registry, host-gate and head-envelope disposition. The positional reader proposal `Randomized.blockVal_eq` remains unapplied for the seven gadget-dependent obligations. The pinned Mathlib source places rational cyclotomic irreducibility in `Cyclotomic.Roots`, outside the scoped replay cache. [Coordination](https://github.com/Shilun-Allan-Li/tcslib/blob/aff0a82679c201834415cbe293393fef7477f6e7/briefs/lwe-sis-constructions/gates/08-construction-statements/COORDINATION.md)

**N02 · PW10 preflight.** The June 4, 2010 author PDF is 44 pages and 557,098 bytes, with SHA-256 `74f48b0eff6f4a0afd52ffe2bfddc6bef006c241c458812bfe085ce85059752c`. The exact Georgia Tech author copy reproduces all seven page hashes and the combined layout-text hash for pp. 33–39. Section 6.2 uses the same shared-matrix, independent-secret column hybrids. Section 6.3.2 gives the gadget, retained-secret cancellation and image factorization. Lean uses an exact dyadic scale and deterministic entrywise bounds in place of PW10’s rounding discrepancy and Gaussian tail. Section 6.4 gives the signed wrap, negative designated shift and enlarged signed message space. Scoped ingestion and approved matching remain pending. [Author PDF](https://sites.cc.gatech.edu/fac/cpeikert/pubs/lossy_tdf.pdf#page=33) · [Source manifest](https://github.com/Shilun-Allan-Li/tcslib/blob/aff0a82679c201834415cbe293393fef7477f6e7/briefs/lwe-sis-constructions/fills/07-sis-trapdoor/pw10-primary-source.json)

**N03 · Construction scope.** Efficient samplers and schedules, the asymptotic primitive and game bridges, other-branch inversion, strong one-time signatures and CCA2 remain separate. SIS hardness stays independent of DLWE.

**N04 · Landing.** Carry the #255 reader prerequisite and the pinned target through the exact-target and six export checks for #250. Merge approval remains with the user. [Reader landing record](https://github.com/Shilun-Allan-Li/tcslib/blob/6410ad6375afe46dcea23b882dcf7eab302fe78e/briefs/lwe-sis-constructions/prerequisites/01-probability-readers/LANDING.md)

**Notation.** `m` in the SIS row is the column count. In the gadget calculation, $m$ is the small residue, $z$ its perturbed encoding, $e$ the signed error and $t$ the integer wraparound quotient. $b,a,u$ are the small-modulus, scale and branch-width exponents. $q$ is the large modulus, $N,d,w$ are input length, secret dimension and concealer width, $B$ is the entrywise error bound and $k$ is the loss in bits. $A,T,E,x$ denote the public matrix, retained secret matrix, integer error matrix and binary input. `val` is the canonical residue representative.
