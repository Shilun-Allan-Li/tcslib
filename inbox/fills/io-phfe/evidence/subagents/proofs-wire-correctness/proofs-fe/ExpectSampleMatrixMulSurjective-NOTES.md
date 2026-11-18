# expect_sample_matrix_mul_of_mulVec_surjective full candidate

Status: scratch FULL candidate checked by inspection only; native proof verification pending.
No Lean/lake/build/Git/live edit/extra agent was run. Exact natively searched doc/header
byte-preserved; one tactic block, no remaining holes/sorry, ≤100 columns. No additional
helper theorem or private generic fiber/counting proof was introduced.

## Existing quotient/fiber route

1. Matrix.mulVec_surjective_iff_exists_right_inverse gives R with M*R=1. This is a proof
   witness among known scalar matrices, not a sampler or an inverse encoding. Multiplication
   S->M*S is exactly the existing Matrix.addMonoidHomMulLeft M. Its surjectivity follows
   with preimage R*U by matrix associativity and the right-inverse equality.
2. Equiv.sigmaFiberEquiv decomposes the coefficient space into its actual output fibers.
   The EXISTING AddMonoidHom.fiberEquivKerOfSurjective identifies each fiber with f.ker;
   Equiv.sigmaEquivProdOfEquiv assembles the output×kernel equivalence e. No fiber-translation,
   equal-fiber-cardinality or finite-sum theorem is re-proved. The additive API is the
   published to_additive declaration in Mathlib GroupTheory/Coset/Basic.
3. The first projection of e is M*S definitionally; hFst uses the explicitly permitted rfl
   reduction of Mathlib/core constructions and local aliases. No definition is passed to
   simp/rw/unfold. The kernel coordinate's internal proof-only choice is never evaluated or
   used by an algorithm; no source-group element is assigned a scalar witness.
4. expect_sample_equiv reindexes along e. Bridge.expect_sample_pair reads uniform output ×
   kernel as sequential samples. The test depends only on output, so expect_const integrates
   out the kernel coordinate. This gives the exact arbitrary-test expectation equality.

The only sigma type appears INSIDE an existing mathematical equivalence. No Fintype/Sigma
blanket instance is declared, and no sigma sample is taken. Existing finite matrix/subtype/
product instances and the kernel's zero element supply sample finiteness/nonemptiness.
No UniformSampler/product sampler or machine is constructed. All dimensions, including
zero rows/columns/inner dimension under the original surjectivity premise, are retained.
The local hf :=?_ includes the required swap before its proof bullet.

## Valid native reuse search evidence (root-run, read by this agent)

Read evidence/search/mddh-finite-linear/run2/results.jsonl, the repaired probe source,
and probe-import-repair.txt. UniformMatrixImageExact: rc1, exactly one expected cannot-close
error, no typing errors/warnings/sorry. UniformMatrixImageApply: rc0, only partial wrappers,
one scratch sorry/two warnings. Scope imported Exponents, Probability, OneWayFunctions.Basic,
GeneralLinearGroup.Card, NonsingularInverse and core Lean.Elab.Tactic.LibrarySearch.
Run1 used nonexistent Mathlib.Tactic.LibrarySearch and is INVALID; retained repair evidence
is not counted as a reuse proof or statement-validation result. No proof pass is claimed.

## Actual static searches / exact reused declarations

Searched finite-fiber/cardinality/reindexing and matrix linear-map API families before writing.
A concrete existing matrix additive hom and fiber-to-kernel equivalence were found, replacing
the initially considered new local uniform-linear helper/quotient counting subproof.

* Mathlib/Data/Matrix/Mul.lean:400, Matrix.addMonoidHomMulLeft, with published apply simps;
  read :390-415. This existing constructor avoids manually defining another additive hom.
* Matrix/NonsingularInverse.lean:322, mulVec_surjective_iff_exists_right_inverse; read exact
  theorem :317-333 and used its A:=M parameter. Matrix.mul_assoc/one_mul finish hf.
* GroupTheory/Coset/Basic.lean:488 (MonoidHom.fiberEquivKerOfSurjective with to_additive
  AddMonoidHom.fiberEquivKerOfSurjective); read :452-494 and exact kernel equivalence type.
  Also found card_fiber_eq_of_mem_range (GroupTheory/Index:919), but no count proof needed.
* Logic/Equiv/Sum.lean:231, Equiv.sigmaFiberEquiv; read :225-244.
* Logic/Equiv/Defs.lean:627, sigmaCongrRight; :716, sigmaEquivProd;
  :722, sigmaEquivProdOfEquiv; read their actual toFun first-projection behavior.
* Games/Probability.lean:304, expect_sample_equiv, and Games/Bridges/Experiments.lean:80,
  expect_sample_pair; expect_bind/pure/const are the existing expectation readers.
* LinearAlgebra/Isomorphisms.lean:41, quotKerEquivOfSurjective, was inspected as an
  alternative; the existing additive fiber equivalence gives the direct output×kernel
  decomposition without extra quotient probability/counting machinery.

A broad initial output was truncated, then narrow exact ranges above were read. An attempted
Matrix/Defs.lean search path did not exist; actual matrix additive-hom definitions were found
in Data/Matrix/Mul.lean. No result depends on a missing path.

## Integration / import status and limits

Suggested source remains cycle-free MatrixDH/FiniteLinear.lean. Existing probe roots supply
matrix right-inverse theory. Precise additional reader roots, only if absent from its closure:
Mathlib.GroupTheory.Coset.Basic (additive fiber API), Mathlib.Logic.Equiv.Sum (sigma fiber),
TCSlib.Cryptography.Games.Bridges.Experiments (pair expectation). No new import was edited or
fetched here; root checks cache/bootstrap requirements. No Games.Closeness/sampler import.

Native focus: the generated PUBLIC additive fiber API name/type, definitional set-fiber vs
Eq-subtype matching in the equivalence composition, standard Fintype/Nonempty kernel instances,
and hFst's projection reduction. The mathematical target is discharged by existing APIs;
if a typing gap appears, isolate it rather than introduce another generic fiber lemma.
This candidate is independent of all MDDH/Linear game admissions and contains no hidden
small-row or rank-probability premise beyond the original hM.
