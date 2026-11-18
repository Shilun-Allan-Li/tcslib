# Encoding injectivity and polynomial-bound proof preparation

Seventeen unelaborated body candidates cover all existing nonreader Encoding.lean
obligations. No source definition, theorem statement, import, or checkout file was
changed. No Lean, Lake, build, cache, exact?/apply?, git mutation, or agent spawn was
performed. This is mathematical review and source-text reuse planning, not kernel
validation. Every proof body is intended for its existing Params namespace/context.

Snapshot HEAD `55cb1147ff84f750a6b94f48103f6cc72d4fa036`; Encoding.lean SHA256
`84a575d4717089eff2f4c37a04e1e3b4af9ff3c5eadbaf1043e37d54f0496dca`. static-checks.json also binds Params, BoolPRG, and the shared encoding API
sources inspected. All candidates remain dependent on explicitly pending earlier
results; compiling against their current sorry bodies would not validate them.

| Existing obligation and source line | Candidate | Necessary inputs |
| --- | --- | --- |
| ell_le_ellBound :408 | bounds/01-ell_le_ellBound.proof | ell/ellBound readers; PolyExpr evaluation equations. |
| n_le_nBound :413 | bounds/02-n_le_nBound.proof | ell_le_ellBound; natural power monotonicity. |
| m_le_mBound :418 | bounds/03-m_le_mBound.proof | n_le_nBound, G.outLen_le, eval_subst/eval_mono. |
| W_le_ell_add_one :425 | bounds/04-W_le_ell_add_one.proof | Rational delta bounds and public floor/rpow facts. |
| W_le_two_pow_ell_add_one :431 | bounds/05-W_le_two_pow_ell_add_one.proof | W_le_ell_add_one, Nat.lt_two_pow_self. |
| B_le_bucketBound :437 | bounds/06-B_le_bucketBound.proof | Params.W_pos, m_le_mBound; public division order. |
| rc_le_rcBound :442 | bounds/07-rc_le_rcBound.proof | W_le_ell_add_one, ell_le_ellBound; w<=w^2. |
| sLen_le_sVarBound :447 | bounds/08-sLen_le_sVarBound.proof | Dimension, B, and rc bounds; power/product/sum order. |
| pubLen_le_seedBound :453 | bounds/09-pubLen_le_seedBound.proof | n_le_nBound; public length/PolyExpr readers. |
| privLen_le_seedBound :461 | bounds/10-privLen_le_seedBound.proof | sLen_le_sVarBound; private length/PolyExpr readers. |
| encBuckets_injective :469 | injective/01-encBuckets_injective.proof | Planned fixed-width list injection helper; numeral injection and List.ofFn_injective. |
| encIdx'_injective :477 | injective/02-encIdx_injective.proof | encBuckets_injective; G.encIdx_injective; shared pair/matrix injection. |
| encIdDraw_injective :485 | injective/03-encIdDraw_injective.proof | encBuckets_injective; G.encIdDraw_injective; shared pair/matrix injection. |
| encOneDraw_injective :493 | injective/04-encOneDraw_injective.proof | Planned fixed-width list injection; W bit bound, prime width; shared vector/numeral/pair injection. |
| encDraw_injective :501 | injective/05-encDraw_injective.proof | encOneDraw_injective; both planned fixed-width list helpers; List.ofFn_injective. |
| encSeed'_injective :509 | injective/06-encSeed_injective.proof | Existing shared pair/vector injection and PrimeParam.le_two_pow. |
| encIdx'_length_le :517 | length/01-encIdx_length_le.proof | Planned exact fixed-width list length; G.encIdx_length_le; numeric/polynomial bounds above. |

## Fixed-width list coordination and explicit pending gap

These candidates consume exactly the staged shared plan in
../FixedWidthList/README.md:

- Internal.encodeList_injective_of_fixedWidth, with supplied block injection and
  an exact common width;
- Internal.encodeList_length_of_fixedWidth, giving len*(width+1)+1 exactly.

Their proposed owner is LPN.lean's area-local StructuredSeed.Internal namespace,
which Encoding already sees through Params. This packet does not add a helper,
copy a parser proof, reach private declarations, or propose another predicate.
The helper declarations are PLANNED, not currently public proved APIs. Root must
complete its required theorem search, elaborate/prove them, and inspect their
axioms before these dependent candidates become validated proofs.

BoolCircuit.encodeList_nil/cons (Uniform.lean:96/100) are existing public readers.
Uniform.lean's prefix-free infrastructure and generic upper bound are private.
The separate helper plan explicitly discloses that overlap and the absence of a
suitable public constant-width counterpart in the present closure. Its precise
reuse investigation is retained there; it is not repeated here. No broad circuit
or emitter import is requested.

Exact element widths used here:

| Payload | Constant width for fixed kappa/pp |
| --- | --- |
| bucket numeral | B |
| selector/residue pair | 2*(ell+1)+2+(kappa+1) = 2*ell+kappa+5 |
| one secret/noise draw | 2*ell*(kappa+1)+3+n*(2*ell+kappa+6) |

These widths are independent of the encoded value. The entire Draw code has length
2*n+3+kappa*(OneLen+1). The constant-width route is valid for these construction
encodings. It must NOT be applied to Raw LPN's different variable-width Nat.bits
selector encoding, which remains the separate issue recorded by design_audit.

## Existing public APIs selected

| Public source/name | Location | Use |
| --- | --- | --- |
| Candidates.length_natToList, natToList_injOn | Candidates/Arithmetic.lean:107,161 | Exact numeral widths and injection below 2^width. |
| Turing.pairEncode_injective, length_pairEncode | Complexity/TuringMachine/Encoding.lean:173,220 | Split encoded pairs; exact pair cost 2*left+2+right. |
| Encoding.Modular.encodeVector_length / encodeMatrix_length | Cryptography/Encoding/Modular.lean:79,89 | Exact field-vector/matrix block counts. |
| Encoding.Modular.encodeVector_injective / encodeMatrix_injective | same :101,126 | Faithfulness for modulus<=2^width, including empty dimensions. |
| List.ofFn_injective | Mathlib/Data/List/OfFn.lean:192 | Recover actual Fin-indexed functions; no chosen finite enumeration. |
| PolyExpr.eval_const/var/add/mul/pow/subst | Complexity/Randomized/PolyExpr.lean:115-134 | Read syntactic polynomial bounds. |
| PolyExpr.eval_mono | same :142 | Reindex G output/index bounds at nBound. |
| Nat.div_lt_iff_lt_mul | Lean Init/Data/Nat/Div/Basic.lean:304 | Rounded quotient bound using W>0. |
| Nat.le_mul_of_pos_right, Nat.le_pow, Nat.lt_two_pow_self | Lean Init/Data/Nat/Lemmas.lean:616,1239,1227 | A<=A*W, w<=w^2, numeral capacity. |
| Nat.floor_le, Nat.one_le_floor_iff | Mathlib/Algebra/Order/Floor/Semiring.lean:43,102 | Floor/max-one upper estimate on positive ell. |
| Real.rpow_mul_natCast, rpow_le_rpow_of_exponent_le, one_le_rpow | Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:498,595,662 | Square the width bound and use 0<delta<1. |
| pow_le_pow_left₀ | Mathlib/Algebra/Order/GroupWithZero/Unbundled/Basic.lean:451 | Monotonicity when squaring the nonnegative real width. |

W_le_ell_add_one's candidate is the SAME Encoding-owner candidate previously
prepared in Stretch/helpers/05; it is organized here for the owning obligation,
not proposed as a second source theorem. On ell=0, real zero-power with positive
delta/2 gives W=1. On ell>=1, max-one equals the floor because ell^(delta/2)>=1;
floor<=real power, and squaring yields W<=ell^delta<=ell. This is the only analytic
upper estimate needed by this packet. SP-W1's rational delta is merely coerced to
real in this analysis. The selector fit follows W<=ell+1<2^(ell+1).

For B, let A=m*kappa. Public division order gives
(A+W-1)/W < A+1 because A<=A*W and W>0. Thus the rounded quotient is <=A,
including A=0; max 1 is <=A+1. Replace m by mBound. This is an owner-specific
bound application, not a new generic ceiling/division theorem.

The remaining count bounds use monotonicity of Nat addition, multiplication and
powers and the owner-side readers. No generic polynomial-bound fact is reproved.

## Exact index constant and all-parameter audit

Write g=length(G.encIdx(n) I). The nested pairs cost

  2*g+2 + (2*bucketLength+2+matrixLength).

The bucket list has length m*(B+1)+1 and matrix length n*ell*(kappa+1), so

  length(encIdx') = 2*g + 6 + 2*m*(B+1) + n*ell*(kappa+1).

The declared idxBound has precisely this constant 6. Its primitive index term uses
idxBits.eval(nBound.eval kappa), sufficient by G.encIdx_length_le and eval_mono.
Each other product is bounded componentwise; no tag or pair separator is dropped.
Both pubLen and privLen fit seedBound individually. The private reader has two
sLen copies, exactly matching the 2*sVarBound in the declared seed polynomial.

At kappa=0, E>=1 and D>=1 imply ell=n=0, while t=rc=0. Positive delta gives w=W=1;
B=max 1(0)=1, sLen=1, pubLen=1, privLen=0. The bound polynomials satisfy
ellBound(0)=nBound(0)=rcBound(0)=0, bucketBound(0)=sVarBound(0)=pubBound(0)=1,
seedBound(0)=1, mBound(0)=G.outBound.eval 0. For arbitrary m0=G.outLen 0,
encBuckets has length 2*m0+1, the matrix has length 0, and

  length(encIdx') = 2*g+6+4*m0
                 <= 2*idxBits.eval 0+6+4*outBound.eval 0.

The zero-parameter Draw domain is a singleton: both the Boolean vector and the
repetition function are empty. encOneDraw and encDraw are each the three-bit
pair of an empty word and the false list terminator. The index/draw domains retain
exactly the supplied Boolean primitive component; the other coordinates are unique.
The published seed has one residue public coordinate and zero private coordinates;
PrimeParam 0 forces p=2, so kappa+1=1 bit still distinguishes its residues.
The noise-selector width is ell+1=1 and its Fin W domain has only selector zero.
Hence all injection claims retain their data at zero as well as positive parameters.

No false or unprovable-as-stated obligation was found in this mathematical audit.
No binder, encoding, constant, asymptotic threshold, or assumption was changed.
Remaining uncertainty is mechanical elaboration, especially implicit pair arguments,
local constant encoders passed to the planned list helper, exact reader occurrence
rewrites, and casts in the floor/rpow proof. No kernel success is claimed.

## Source-text checks

reuse-searches.json records eleven successful text searches and exact output.
import-closure.json follows actual imports with comments/strings removed. Every
selected existing API is in the current Encoding closure; no new import is needed.
This closure is not the ledger of direct Mathlib cache roots, and no cache command
was run. static-checks.json and SHA256SUMS record candidate counts/widths/tactic
blocks and hashes. Those checks neither parse nor elaborate Lean.
