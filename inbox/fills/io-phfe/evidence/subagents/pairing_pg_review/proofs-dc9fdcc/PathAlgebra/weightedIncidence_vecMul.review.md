# weightedIncidence_vecMul proof candidate

Exactly one existing theorem proof is supplied. Its header and full current docstring
match live PathAlgebra.lean; the fragment changes only its body. It contains one tactic
block and no admissions or additional helper declarations. The lead must validate it;
the agent ran no Lean, lake, Git, live edit or proof check.

The lead has already run the required helper searches with corrected typing and section
closures. The agent read:

- evidence/search/path-algebra/run2/mods/.lake_io-phfe-probes_PathAlgebraReuse2.log;
- evidence/search/path-algebra/run2/mods/.lake_io-phfe-probes_PathAlgebraApply2.log.

The exact? run has three unresolved helper goals, with no typing errors. The apply?
run gives partial function-equality suggestions, not a complete public theorem.
Focused source searches are saved in weightedIncidence_vecMul.searches.txt.

## Reuse and Rule 10

1. `change` identifies the explicit entrywise-difference matrix with the difference of
   two `Matrix.of` matrices. Only core/Mathlib pointwise operations reduce here.
2. `Matrix.vecMul_sub`, Data/Matrix/Mul:1010, performs the matrix-action subtraction.
3. `Matrix.vecMul_eq_sum`, Data/Matrix/Mul:694, publishes the coordinate action as a
   sum of scaled rows. No definition of vecMul or dotProduct is unfolded or passed to
   simp/rw; the already proved coordinate equation is used.
4. `Finset.sum_apply`, generated from Algebra/BigOperators/Pi:40-43, evaluates each
   finite sum of row functions. `Pi.sub_apply` and `Pi.smul_apply`, generated in
   Algebra/Notation/Pi/Defs, evaluate the pointwise operations; `Matrix.of_apply` from
   LinearAlgebra/Matrix/Defs:83 evaluates the explicit rows.
5. `smul_eq_mul`, Algebra/Group/Action/Defs:68, and `mul_ite`, Algebra/Notation/Defs:109,
   give the two conditional scalar sums. `mul_zero`, `mul_one`, and `eq_comm` finish
   their displayed form. eq_comm changes only equality predicates, not products.

The proof composes existing subtraction, coordinate-sum and conditional-multiplication
laws. It does not reprove finite-sum linearity or the multiplication-through-conditional
lemma inline. No TCSlib definition or new admission is consumed, and no new import is
needed beyond the current PathAlgebra imports.

It retains multiplication order flow*weight, so arbitrary noncommutative and trivial
rings remain valid. No node-finiteness, edge-equality, injectivity, positivity, or
inhabitedness assumption is introduced. Empty edge types and repeated/loop endpoints
are included. No mathematical obstruction was found.
