# Quadratic.cross_tensor_identity candidate

Status: full scratch candidate checked by inspection only, native verification pending. No
Lean, lake, build, Git, live edit, or additional agent was run. Frozen header and statement
prose copied byte-for-byte; one tactic block, no remaining holes/sorry, ≤100 columns. No new
helper declaration or statement change. This scalar-only result needs no group inputs or
R-DLOG/scalar-existence assumptions. It covers zero n1/n2: a nonexistent output coordinate
is handled by the canonical equivalence's surjectivity, without a positivity hypothesis.

## Proof decomposition

The local top/bottom aliases are exactly the two Kronecker blocks named by mixScalar_eq.
Reindex the output q by finProdFinEquiv. Then obtain the two concrete block contributions
by specializing the existing Matrix.mul_kronecker_mul (no generic mixed-product reproof):

* hTop uses row matrices S1:Fin 1×Fin 2, Z2:Fin 1×Fin n2. The four inputs are
  S1,A1,Z2,1_n2. Select row (0,0) and column (i,j), use Matrix.mul_one and the published
  Kronecker/product entry readers. This gives (s1 A1)_i * z2_j.
* hBottom uses Y1:Fin 1×Fin n1 and S2:Fin 1×Fin 2. The four inputs are
  Y1,1_n1,S2,A2. The same row selection gives y1_i * (s2 A2)_j.

hCross reindexes the existing signal/mixing dot product through signalCoord using
comp_equiv_dotProduct_comp_equiv. signalScalar_eq/mixScalar_eq/privateTensor_eq and the
canonical inverse readers expose the two Sum.elim branches. The published
sumElim_dotProduct_sumElim splits the blocks. No sums, finite equivalences, or generic
Kronecker row-action machinery are rederived. After hTop/hBottom, the final coordinate
identity is `(a+z1)(b+z2)=z1*z2 + (a*z2+(a+z1)*b)`, closed by ring.

The local hTop/hBottom/hCross are coordinate facts within this existing frozen theorem,
not added generic helper APIs. All foreign TCSlib definitions are read through their
published readers; no generated equation or definition is passed to simp/rw/unfold. The
change steps only identify Mathlib dot products/vecMul and local let aliases by reduction.

## Actual search/read record

All paths below are in the current live worktree; no Git was used.

* `rg -n 'cross_tensor_identity|mixScalar_eq|signalScalar_eq|privateTensor_eq'` over
  QuadraticCorrect.lean and Quadratic.lean, followed by a narrow complete read of the
  frozen target and the readers. Read Classes.lean:280-299 for privateTensor_eq.
* `rg -n 'vecMul|mulVec|vecMulVec|mul_kronecker_mul|kronecker.*(add|sub)|add_kronecker|sub_kronecker'`
  in Mathlib/LinearAlgebra/Matrix/Kronecker.lean located mixed-product and distributive laws.
* `rg -n 'vecMul.*kronecker|kronecker.*vecMul|mulVec.*kronecker|kronecker.*mulVec|vecMulVec.*kronecker'`
  over Mathlib and TCSlib found Mathlib/LinearAlgebra/Matrix/Vec.lean:120,136. Read :108-141:
  vec_vecMul_kronecker is an alternative using column-vectorization and transposition, which
  adds unnecessary layout translation here. Reused mul_kronecker_mul with single-row inputs.
* `rg -n 'comp_equiv_dotProduct_comp_equiv'` over TCSlib/Mathlib located the published
  dot-product permutation law at Data/Matrix/Mul.lean:139; read the adjacent Sum/dot laws.
* `rg -n 'theorem vecMul_apply|lemma vecMul_apply|theorem vecMul.*comp|vecMul_submatrix|vecMul_reindex'`
  over Matrix/Mul and Matrix/Reindex found no directly matching canonical block action law.
* `rg -n 'signalScalar.*mixScalar|privateTensor.*vecMul|cross_tensor'` over TCSlib found
  only the existing target; no new helper was needed.
* An initial signalCoord search named nonexistent Wee20/Parameters.lean; corrected to the
  actual Quadratic.lean definitions. No conclusion is based on the missing path.

## Reused exact APIs

* Wee20/Quadratic.lean: signalCoord (64), mixScalar_eq (87), signalScalar_eq (135).
  signalCoord is used as an equivalence; its body is never unfolded.
* Classes.lean: privateTensor_eq (294).
* Mathlib/LinearAlgebra/Matrix/Kronecker.lean: kroneckerMap_apply (60),
  mul_kronecker_mul (369).
* Mathlib/Data/Matrix/Mul.lean: sumElim_dotProduct_sumElim (123),
  comp_equiv_dotProduct_comp_equiv (139), mul_apply' (299), Matrix.mul_one (443).
* Canonical finProdFinEquiv.surjective and Equiv.symm_apply_apply, Function.comp_apply,
  Pi.add_apply; ordinary ring normalization over ZMod.

## Native integration focus

The unchecked details are normal elaboration of single-row matrices supplied as lambdas,
composition/eta matching in hCross, and local let reduction in the two simpa steps. The
single-row matrices can be given explicit local Matrix types if native elaboration needs
more expected-type information; no new mathematical helper or statement change is required.
The two mixed-product instances are exactly typed by their A1/A2/identity operands.
