<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/SmolenskyAlgebra.lean :: rootCubeBadCount -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Error count of a polynomial against a function on `{1, ω}^n`

**Definition.** For finite `K`, a target `f : rootCube ω n → K` and a polynomial
`P : MvPolynomial (Fin n) K`,

`rootCubeBadCount ω f P = #{x : rootCube ω n | P.eval x.1 ≠ f x}`,

the number of cube points where `P` disagrees with `f`. The definition is written in
tactic mode only to insert `classical` for the decidability of the filter.

**Remark.** The root-cube analogue of `badInputCount`, which does the same job on the
Boolean cube `{0,1}^n`. Its arguments are ordered target-then-polynomial; the
symmetric function-to-function version is `rootCubeFunctionBadCount`.

**Used in.** The approximation hypotheses and conclusions of
`rootCube_counting_obstruction`, `rootProd_approx_implies_all_functions_approx`,
`no_low_degree_rootProd_approx`, and their concrete counterparts in
`LowDegreeObstruction.lean`.
