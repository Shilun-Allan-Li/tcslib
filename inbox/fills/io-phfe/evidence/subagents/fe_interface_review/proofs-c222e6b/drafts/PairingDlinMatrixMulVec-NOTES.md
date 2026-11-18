# Pairing.dlinMatrix_mulVec candidate

Status: independent scratch M1 algebra candidate; inspection only, native check pending.
No Lean/lake/build/Git/live edit/extra agent was used. Frozen declaration prose and header
are copied byte-for-byte. Exactly one tactic block, no holes/sorry, no helper or changed
matrix/group/statement. Valid for every modulus p:Nat, including p=0, as frozen.

Proof: read dlinMatrix_eq. Matrix.cons_mulVec recursively reads its three row dot products,
and Matrix.empty_mulVec closes the empty row tail. Matrix.vec2_dotProduct' evaluates each
known two-coordinate dot product; elementary zero/one and addition laws give ar, bs, r+s.
No core/Mathlib/TCSlib definition is explicitly passed to simp/rw/unfold; every named item
in the simp list is a published equation/algebra theorem.

## Actual searches / exact source references

* Read current live Pairing/Linear.lean:1-165, especially dlinMatrix_eq (107) and the
  exact frozen dlinMatrix_mulVec (115).
* `rg -n 'mulVec_(cons|fin|empty)|cons_mulVec|mulVec_fin|mulVec.*of|vec2|vec3|Fin.sum_univ_two|sum_univ_three'`
  over Mathlib Data/Matrix and LinearAlgebra/Matrix located the existing literal-matrix APIs.
* `rg -n '(theorem|lemma) (mulVec_cons|mulVec_empty|mulVec_apply|dotProduct_cons|cons_dotProduct|vecCons|cons_val|sum_univ_three|sum_univ_two)'`
  initially named nonexistent Data/Matrix/Notation.lean; corrected to the actual
  LinearAlgebra/Matrix/Notation.lean. No conclusion relies on the missing path.
* Narrow reads inspected Mathlib/LinearAlgebra/Matrix/Notation.lean:306-338 and :468-511:
  - Matrix.empty_mulVec:316;
  - Matrix.cons_mulVec:324;
  - Matrix.vec2_dotProduct':497.
* Read Matrix/Mul.lean:648-672 for the existing mulVec/dot-product layout; no definition
  unfolding from this source appears in the proof.
* Additional narrow searches/read inspections located Matrix.cons_val_zero/one/succ and
  Fin.sum_univ_two as alternatives. The selected row-recursion readers avoid manual
  finite-index cases or a repeated coordinate-sum proof.

## Import availability

No extra import is proposed. Verified existing textual import route:
Pairing/Linear -> Pairing/Exponents -> Mathlib.LinearAlgebra.Matrix.Hadamard ->
Mathlib.LinearAlgebra.Matrix.Trace -> Mathlib.LinearAlgebra.Matrix.Notation.
The first three matrix reader lemmas above are all in that already-imported Notation module.
The `of` wrappers in cons_mulVec reduce through allowed Mathlib definitional matching;
Matrix.of itself is not passed to a rewrite/simp tactic.
