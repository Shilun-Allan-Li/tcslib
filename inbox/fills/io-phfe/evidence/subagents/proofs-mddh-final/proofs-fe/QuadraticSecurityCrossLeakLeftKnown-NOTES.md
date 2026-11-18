# QuadraticSecurity.crossLeakLeft_known

Scratch-only frozen doc/header replacement. Exactly one12-line proof block; no admissions,
new helper, import, Lean/lake/build/Git command or live edit. Native check pending.
The right-hand counterpart is intentionally untouched for a separate invocation.

## Argument and R-DLOG

The existing expVec_tensor_left theorem already states the complete coordinate identity:
raise the supplied known-y1 exponent vector entry to known scalar y2 to obtain the implicit
private tensor. Read that identity at finProdFinEquiv.symm i and consume privateTensor_eq
and Matrix.kroneckerMap_apply to match the established flattened coordinate order.
Then crossLeakLeft_eq, groupDot_expVec, and value_eq identify the scalar dot product.
The arbitrary supplied group mu stays unchanged as the same inverse factor on both sides.
No logarithm, exponent representative, group encoding inverse, scalar witness or new group
law is introduced; all scalar vectors are existing theorem parameters.

Parent initially suggested crossLeak_known_value, which was read and is now proved.
Its hypothesis is a KNOWN scalar mu and its group argument is g^mu.val. It does not directly
apply to this frozen theorem's arbitrary group mu; using it would require an unnecessary
exponent witness. This was sent to root, who explicitly approved the direct shared
expVec_tensor_left/groupDot_expVec route. There is no statement obstruction or E-STMT.
The matrix-action laws were searched, but the existing vector/tensor action is the exact
more specific reusable API, so no matrix embedding or fresh generic law is needed.

## Actual static search/reuse record

- Read QuadraticSecurity/Theorems:1-180 and located its exact crossLeakLeft_known:90
  and frozen proof sketch/header. Read crossLeakRight_known only to confirm it is separate;
  no right proof was drafted.
- `rg -n 'crossLeakLeft_known|crossLeakRight_known|crossLeak_known_value|crossLeakLeft|crossLeakRight'`
  in Theorems/QuadraticSimulator; then read QuadraticSecurity/Reduction:38-88 for both
  exact mixed-leak readers and QuadraticSimulator:130-205 for crossLeak_eq and
  crossLeak_known_value:164.
- `rg -n 'crossLeak|expMat_mul|expVec_vecMul|matMulGroup|groupMatMul'` in Pairing/Exponents
  and read its matrix-action groupDot transport at380-403. No repeated group algebra is used.
- `rg -n 'pow_val_mul|pow_val.*mul|expVec_apply|expMat_apply|def expVec|def expMat'` in
  Exponents and Group, then read the exact existing tensor lemmas at474-508.
  expVec_tensor_left:483 is the complete required pointwise known-scalar tensor law;
  expVec_tensor_right is left for the separate right invocation.
- Read Quadratic:286-318: value_eq:308 is the exact tensor/evaluation-vector dot product.
- Read Classes:280-301: privateTensor_eq:294 gives the canonical row-major pair indexing.
- Read QuadraticCorrect:58-91 and216-238 for the already proved local parallel.
  signalGroup_exp:74 consumes expVec_tensor_left with the same privateTensor reader and
  canonical coordinate projection. The new proof reuses those PUBLIC statements only;
  it does not copy an inaccessible proof or define a third tensor action.
- groupDot_expVec in Exponents is the shared finite-product-to-scalar-dot-product theorem;
  expVec_apply and Matrix.kroneckerMap_apply are the relevant public coordinate readers.

Only public equation/theorem readers appear in rw/simp. The Fin-product coordinate map
and PNat modulus abbreviation are the existing published/canonical representations.
The frozen docstring, sketch, theorem binders and conclusion were copied mechanically;
only the existing term-sorry body is replaced. No successful native typecheck, seal pass
or standard-only chain is claimed by this scratch draft.
