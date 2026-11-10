# Regev PKE hybrid support proof fill

Draft #250's own branch `cryptography/lwe-sis-construction-statements` fills six
obligations at `8c6b23f5b69260acb66cc99e322a81c4c79f51bb`. Its integrated pre-fill baseline is
`410fdc9fe776bce509226d6e5db235dba6759ee4`, with central #239 merge
`27f9ea89b72d84abaec8128f2abd826f24aaced4`. The combined statement freeze is
`17b2a282b545c6ebca3fccc88d518d18ae78f485`. The 31 previously audited proof bodies
and the new six fills leave 64 owned admissions in the full draft.

| Obligation | Argument |
|---|---|
| Uniform hash difference | Split the matrix at a differing binary coordinate, multiply the distinguished column by a unit and translate, then average the singleton mass. |
| Extraction error | Bound the numerator by the residue width, apply the sample budget to the denominator, and compare with the square of the nonnegative target. |
| Real-to-uniform-key hybrid | Reassociate the independent key, subset and test seeds on both sides, then use the exact decisional LWE advantage equation. |
| Augmentation bijection | Invert row augmentation by transposing the initial rows back and selecting the last row. |
| Augmented ciphertext | Read the matrix product on the initial rows and last row separately, adding the message codepoint only in the last coordinate. |
| Doubled extraction error | Apply the general bound at the augmented dimension and multiply by two. |

Exactly six theorem bodies change. The two overviews and two adjacent hashing
sketches describe the final proofs. The earlier audit's 220 ordered source
declarations and the other 151 frozen paths are reconciled at source level.
The fill uses public equations, local lets and existing Mathlib equivalences.
The proof scope adds zero declarations, imports, facade edits or shared APIs.

| Check | Result |
|---|---|
| Fresh serial seven-facade closure | 144 modules in 454.015 s, zero errors, 64 owned and 17 inherited admission warnings |
| Axiom probe | 80.879 s, 220 source prints and 56 backing-contract prints |
| Owned constant inventory | 589 constants, exactly 64 using `sorryAx`, all six new proofs standard-axiom only |
| Compiler auxiliaries | 0 new, 0 origin changes since the prior inventory |
| Style | Zero failures and two inherited reader warnings over 41 files |

The final sweep started with an empty own `TCSLIB_OLEANS` tree and used this
worktree's existing manifest-pinned packages. The full module order, source
hashes, run records and raw log bytes are in `evidence/`. The raw logs are framed
by byte length and SHA-256. The previous audited inventory and current delta
reconcile the standard axiom sets. Verification covers this closure and the
source freeze. Physical cache provenance and freshness remain maintainer
attestations. System process enumeration was unavailable.

The initial Regev proof attempt stalled. Its check driver was interrupted,
and the user stopped the isolated recorded checker group. The revised proof
writes the two probability equalities explicitly. The next development check
isolated a dependent `Fin.snoc` annotation error, corrected by giving the
augmented rows a typed local name. These attempts are recorded separately from
the final sweep. Later checks inherit the invocation's process group so an
interruption can reach both the driver and the checker.

The universality, entropy and leftover-hash chain still needs the two proposed
owner-side readers. The uniform-key statistical hybrid and final fixed-bit
Regev bound retain their admissions. Efficient sampling, implementation and
CPA game integration are later obligations. #250 also retains its other shared
owner holds and scoped source review.

**Not yet clear to merge.** This fill awaits its combined proof audit and #250
has 64 other proof obligations.
