# QuadraticSecurity.crossLeakRight_known

Scratch-only exact frozen doc/header replacement. Exactly one12-line tactic block, no
admissions, public helper or import. No Lean/lake/build/Git command or live edit was used.
Native check pending. The left proof and all live code are untouched.

## Reuse / mathematical argument

The shared expVec_tensor_right theorem directly handles the swapped known-scalar exponent
order: its right-vector group entry is powered by the known left scalar, and its result
is the scalar tensor in the same left*right coordinate order. Read it at the canonical
finProdFinEquiv.symm coordinate and match privateTensor_eq via kroneckerMap_apply.
Then crossLeakRight_eq exposes the exact frozen groupDot, groupDot_expVec reads its
scalar dot product, and value_eq is exactly that scalar value. The arbitrary group mu
remains the unchanged inverse factor. No exponent representative, logarithm, inverse
encoding or scalar witness is introduced. No additional generic group lemma is needed;
the shared right-tensor law already includes scalar commutativity.

The small coordinate assembly mirrors the requested existing left theorem; it reuses the
published generic tensor action and does not copy or reprove its finite-product/group
arithmetic. No inaccessible/private lemma is referenced.

## Actual static searches/read record

- Read current QuadraticSecurity/Theorems:98-115 to confirm the right statement is still
  the requested admission, and copy its exact M0 prose, sketch, binders and conclusion.
- Read QuadraticSecurity/Reduction:63-84: crossLeakRight_eq:73 supplies its complete group
  formula with right group vector and known left scalar powers.
- `rg -n 'expVec_tensor_right|crossLeakRight_known|crossLeakRight_eq'` over Pairing/Exponents
  and QuadraticSecurity. The precise shared theorem is Exponents:496.
- Read Exponents:492-506 for the exact right-tensor API and its complete existing proof.
  It already outputs `expVec g (fun ij => a ij.1 * b ij.2)`, so no extra mul_comm proof
  or scalar transport is rederived here.
- Read Classes:292-299: privateTensor_eq:294 is the canonical flattened product reader.
- Read Quadratic:306-316: value_eq:308 is the exact privateTensor/eval-vector dot product.
- Read the preceding left scratch replacement solely to keep the two established
  coordinate conventions aligned. Its native status is not assumed or claimed here.

Only crossLeakRight_eq, the existing tensor/exponent readers, privateTensor_eq,
Matrix.kroneckerMap_apply, groupDot_expVec and value_eq are consumed. No foreign public
algorithm occurs in an unfold/simp body list. Frozen header/prose are mechanically
unchanged; only the original term-sorry body is replaced. Successful native elaboration,
seal and standard-only status remain root checks, not claims of this draft.
