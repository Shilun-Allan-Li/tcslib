# Wire serialization adapters: header/static-search proposal only

NO proofs, native searches, Lean/lake/Git commands, live edits, new runtime definitions,
or new Mathlib roots were made. The four admitted headers are for statement review and
root-native search only. All probes use term-form exact?%, hence ZERO tactic blocks.

## Scope and proposed home

Proposed new owned Wee20/WireLemmas.lean imports exactly Wee20.Wire and Pairing.MatrixDH.Defs.
The probes add only permitted core Lean.Elab.Tactic.LibrarySearch. No probe imports the
new WireLemmas stub, PHFE.Encodings, or another probe. Every probe has an anonymous
example, preventing the target itself or another admitted adapter from satisfying search.
The target context is Wire's existing namespace and normal G/kappa/public-parameter types.

The direction is cycle-free: MatrixDH.Defs does not depend on Wee20/Wire, and Wire does
not depend on WireLemmas. PHFE.Encodings can consume WireLemmas at integration. Do NOT
import WireLemmas from Wire itself. Root should expose the new proof module from the
existing Wee20 facade as appropriate; this scratch task changes no imports/exports live.

## Exact representation/reuse result

Wire.groupMatrix is EXACTLY BilinearGroup.groupMatrixEnc pp.group after reading ONLY
Wire.groupMatrix_eq, Wire.groupVector_eq and BilinearGroup.groupMatrixEnc_eq. Both use
row-major List.ofFn blocks with the same point encoding, row order and flatten nesting.
The existing base theorem proves exact length m*n*wG and injectivity for every shape.
It MUST supply both mathematical facts; do not reproduce length_flatten sums or the
base proof's fixed-row/point-block injectivity. The four proposed wrappers are interface
adapters, not independent counting/faithfulness proofs.

For vectors use a ONE-ROW matrix fun (_ : Fin 1) j => v j and the SAME base API.
Its outer List.ofFn/flatten reduces using existing ofFn_succ/ofFn_zero and
flatten_singleton (or ofFn_const and singleton equations). This is representation glue,
not a new flatten count. Matrix injectivity yields equality of the sole rows by reading
coordinate 0. There is no exponent extraction or scalar representative assumption.

No positive width/dimension premise is needed: the existing base API covers empty
shapes. Every proposed length uses the actual G.wG.eval kappa; no schedule is computed.

## Do fewer bridge helpers suffice?

Recommend exactly the FOUR requested public APIs and ZERO additional equality bridges.
Separate public theorems groupMatrix_eq_groupMatrixEnc or oneRow_enc_eq would merely
package a reader rewrite and singleton reduction used by these adapters. They need
not become new reusable statements or native-probe obligations.
Two matrix adapters alone would technically suffice if every vector consumer repeated
its one-row conversion, but that repeats interface plumbing across length/injectivity
consumers. The four small wrappers give a clean consumer API while all substantive
mathematics still comes from the single existing matrix encoding implementation.

## Nine PHFE.Encodings obligations and what these adapters supply

| Existing admission | Group adapter reuse | Other existing APIs / boundary |
|---|---|---|
| quadraticMPK_length | groupMatrix_length | Wire MPK readers, length_pairEncode, mpkLen_eval, piDim_eq plus PolyExpr readers |
| quadraticMSK_length | groupMatrix_length | Modular.encodeMatrix_length, pair lengths, mskLen_eval |
| quadraticCT_length | groupVector_length | Wire CT readers, List.length_append, ctLen_eval |
| keyWord_length_le | groupMatrix_length | original bits length, pair lengths, PG.auxCount_add_one, mCount_le_mBound, skLen_eval |
| encMPK_injective | groupMatrix_injective | exact-length pad recovery, pairEncode_injective, coordinate equivalence surjectivity, record fields |
| encMSK_injective | groupMatrix_injective | exact-length recovery, modular matrix injectivity, existing order-width bound, pair/record fields |
| encSK_injective | groupMatrix_injective | recover ORIGINAL function prefix first; only then align dependent node coordinates and actual word lengths |
| encCT_injective | groupVector_injective | exact word recovery, fixed-length append cancellation, CT record fields |
| quadraticSimState_injective | groupMatrix_injective | nested pair injectivity, Wire state/scalar readers, modular vector/matrix injectivity and coordinate equivalences |

Existing pairEncode_injective separates nested pair blocks; do not build a new parser.
Core List.append_inj_left/right split equal ciphertext concatenations once the proposed
length readers identify the fixed boundary. Existing ofFn_padFin_of_length recovers
exact-length words. For bounded key words, zero padding is NOT injective on arbitrary
variable-length lists: encSK needs its frozen sketch's original-function-prefix step,
then fixed actual lengths. These four adapters alone do not justify skipping that step
or replacing a noncanonical original function word with its decoded tensor.

PG.auxCount_add_one relates auxiliary rows to non-output nodes, and mCount_le_mBound
then supplies the required uniform key bound; no unprovided separate aux bound is needed.
The existing BB1Machine.order_le_two_pow covers scalar modular injectivity; do not
reprove order/cardinality bounds or use any BB1 draw/decoder. No target/efficiency
hypothesis is needed for these raw wire algebra facts.

No false/vacuous statement was found among the four proposed headers. The nine original
proofs still need their own dependent-framing and fixed-width arithmetic work; no claim
of their completion is made here.

## Native gate

Run probes/order.txt through root's authorized native wrapper; term exact?% has the
same no-required-term depth-6 library search as exact?. Confirm clean target typing,
then distinguish complete proofs from cannot-close diagnostics/timeouts. Root's native
apply? probes remain required before a new helper proof block is authorized. No
apply tactic source is generated in this zero-tactic-block design invocation.
