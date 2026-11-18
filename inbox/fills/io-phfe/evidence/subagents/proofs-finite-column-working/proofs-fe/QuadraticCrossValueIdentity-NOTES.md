# Quadratic.cross_value_identity candidate

Status: scratch full candidate, inspection only, native pending. No Lean/lake/build/Git/live
edits were performed. Frozen header/prose preserved exactly. One tactic block, no remaining
holes/sorry, no helper or statement change. Its substantive dependency cross_tensor_identity
is still native pending, so this is not a standard-only chain claim.

Apply congrArg (fun v => dotProduct v fx) to cross_tensor_identity. The published
add_dotProduct reads the sum, and reverse Matrix.dotProduct_mulVec moves the mixing matrix
onto fx. The resulting equation is maskedValue = privateValue + crossValue;
eq_sub_of_add_eq applied to its symmetric equality gives the target. Both statement lets
reduce definitionally; no definition is passed to simp/rw/unfold, and no tensor semantics
are redeveloped.

## Actual source searches/reads

* Read current live Wee20/QuadraticCorrect.lean:89-128 for the exact two frozen headers.
* Read Mathlib/Data/Matrix/Mul.lean:108-120 and :706-716 for add_dotProduct (115) and
  Matrix.dotProduct_mulVec (710).
* `rg -n 'eq_sub_of_add_eq'` over FE and Algebra/Group/{Basic,Defs}.lean located the
  additive theorem at Algebra/Group/Basic.lean:697-698, generated from
  eq_div_of_mul_eq' with shape a*c=b -> a=b/c, hence a+c=b -> a=b-c.
* `rg -n 'theorem (eq_div_of_mul_eq|eq_sub_of_add_eq)|lemma (eq_div_of_mul_eq|eq_sub_of_add_eq)'`
  over Algebra/Group confirmed the relevant orientation.
* `rg -n 'congrArg.*dotProduct|add_dotProduct.*at|dotProduct_mulVec.*at'` over FE found
  nearby established dot-product congruence use in PartialGarbling/PathAlgebra.lean:59.

All dependencies apart from the pending existing cross_tensor_identity are published
Mathlib algebra equations. No new helper or native reuse probe is needed.
