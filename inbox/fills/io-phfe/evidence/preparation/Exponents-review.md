# Exponents draft inventory

Draft: /private/tmp/io-phfe-drafts/Pairing/Exponents.lean
Intended destination: TCSlib/Cryptography/Pairing/Exponents.lean
Base read: 5ed465f62e4ae0f93ded1a1ba49e807591b589eb.
334 lines; maximum width 95 characters; 12 definitions, 12 term-rfl readers,
20 substantive statement admissions. No tactic blocks. No Lean/lake/check command ran.
Reader elaboration and exact?/apply? probes are deferred to the lead's authorized Lean route.

## Imports

- TCSlib.Cryptography.Pairing.Group: source and target groups, exponent and pairing API.
- Mathlib.Data.Matrix.Mul: Matrix, dotProduct, mulVec, vecMul, matrix multiplication.

No Kronecker module is needed: scalar tensor coordinates use product-indexed vectors, exactly
matching a flattened vecMulVec. These tensor identities should be connected with existing
Matrix.kroneckerMap/vecMulVec ordering readers in the class and scheme modules; this module
introduces no tensor datatype or duplicate Kronecker algebra.

## Public definition/readers

All names below are under TCSlib.Cryptography.Pairing unless the B. prefix is present;
B. means the BilinearGroup namespace and an explicit group argument.

- groupDot / groupDot_eq: product of known powers, generic CommMonoid target.
- groupMulVec / groupMulVec_apply: group matrix, known scalar column.
- groupVecMul / groupVecMul_apply: known scalar row, group matrix.
- groupMatMul / groupMatMul_apply: group matrix times known scalar matrix.
- matMulGroup / matMulGroup_apply: known scalar matrix times group matrix.
- B.expVec / B.expVec_apply: source-group vector representation.
- B.expMat / B.expMat_apply: source-group matrix representation.
- B.expVecT / B.expVecT_apply: target-group vector representation.
- B.expMatT / B.expMatT_apply: target-group matrix representation.
- B.pairVec / B.pairVec_eq: product of coordinate pairings.
- B.pairMat / B.pairMat_apply: pairing matrix product.
- B.pairTensor / B.pairTensor_apply: all pairwise coordinate pairings.

## Substantive statements / nearest relatives

- B.pow_val_add_GT, B.pow_val_neg_GT: disclosed target-group near-copies of source-group
  B.pow_val_add / B.pow_val_neg (Pairing/Group.lean:254,260). No target variants were found.
  Reuse ZMod.val_add and pow_mod_card (Mathlib/GroupTheory/OrderOfElement.lean:1012), B.card_GT.
- B.expVec_add, B.expVec_neg, B.expVec_smul: transport Group.lean:254,260,218 coordinatewise.
- B.expVecT_add, B.expVecT_neg, B.expVecT_smul: target analogues; reuse existing
  B.pow_val_mul_GT (Group.lean:222) and the two disclosed target helper statements.
- B.groupDot_expVec, B.groupDot_expVecT: representation transport for dotProduct
  (Mathlib/Data/Matrix/Mul.lean:67), near generic finite product-of-powers identities
  (Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:646, prod_pow_eq_pow_sum).
  No ZMod exponentiation product helper with these conclusions was found.
- B.expMat_mulVec, B.expVec_vecMul: representation transport for Matrix.mulVec and vecMul
  (Mathlib/Data/Matrix/Mul.lean:658,672), not new scalar matrix algebra.
- B.expMat_mul, B.expMat_mul_left: the same entrywise groupDot representation transport
  for Mathlib matrix multiplication. These are needed on either side for Pi's KeyGen*.
- B.expMatT_mulVec: target-group representation transport, used by reconstruction.
- B.pair_expVec: transport of B.bilinear_pow (Pairing/Group.lean:178) to finite dot products.
- B.pair_expMat: row-column version of pair_expVec; existing scalar matrix product reused.
- B.pairTensor_expVec: coordinatewise bilinear_pow for product-indexed tensors.
- B.expVec_tensor_left, B.expVec_tensor_right: known scalar factor is applied by powers;
  reuse pow_val_mul, pow_mul and scalar commutativity.

Generic group actions and pairing products are new representation plumbing, not new scalar
matrix operations. The generic action definitions work for BOTH source and target groups.
No exponent is recovered from a group element; no choose/invFun/pow-bijective use occurs.

## Actual searches performed

Working directory for these searches:
/Users/seyoonr/.codex/worktrees/tcslib-io-phfe/tcslib-exchange

1. Name search:
   rg -n 'groupDot|groupMulVec|groupVecMul|expVec|expMat|pairVec|pairMat|pow_val_add_GT|pow_val_neg_GT' \
     TCSlib .lake/packages/mathlib/Mathlib/Algebra .lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix
   No matches.
2. Broader name search including all Mathlib and added matrix-action/tensor names:
   rg -n 'pow_val_add_GT|pow_val_neg_GT|def (expVec|expMat|groupDot|groupMulVec|groupVecMul)|pairVec|pairMat' \
     TCSlib .lake/packages/mathlib/Mathlib/Algebra .lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix
   No matches.
3. Shape search:
   rg -n 'prod.*pow|pow.*prod|prod.*sum|sum.*prod' \
     .lake/packages/mathlib/Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean
   Found generic products including prod_pow_eq_pow_sum at line 646.
4. Scalar/representation shape search:
   rg -n 'prod.*\.val|\.val.*prod|pair.*prod|prod.*pair' \
     TCSlib/Cryptography/Pairing .lake/packages/mathlib/Mathlib/Data/ZMod \
     .lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix
   No matches.
5. Existing source API search:
   rg -n 'pow_val_add|pow_val_neg|bilinear_pow|pow_val_mul' \
     TCSlib/Cryptography/Pairing/Group.lean
   Found the published API at lines 178,218,222,254,260.
6. Mathlib reader/source checks:
   rg -n 'mulVec|vecMul' .lake/packages/mathlib/Mathlib/Data/Matrix/Mul.lean
   sed -n '660,733p' .lake/packages/mathlib/Mathlib/Data/Matrix/Mul.lean
   rg -n 'pow_mod_card' .lake/packages/mathlib/Mathlib/GroupTheory/OrderOfElement.lean
   rg -n 'map_prod|map_sum' \
     .lake/packages/mathlib/Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean
   Confirmed Matrix scope for vector-action notation; draft opens scoped Matrix.
7. An initial complex rg regular expression for declaration searches was rejected by rg's
   parser; it produced no search result and was replaced by the simpler successful searches
   listed above.

Pending: exact?/apply? probe for every substantive statement, full-name/short-name clash scan,
M0 elaboration and style/Rule-10 suite. This is a scratch draft, not a certified checkpoint.
