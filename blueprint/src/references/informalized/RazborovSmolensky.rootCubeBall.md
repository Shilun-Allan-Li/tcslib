<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/SmolenskyAlgebra.lean :: rootCubeBall -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Hamming ball around a function on `{1, ω}^n`

**Definition.** For finite `K`, a center `center : rootCube ω n → K` and radius `e : ℕ`,

`rootCubeBall ω center e = {f : rootCube ω n → K | rootCubeFunctionBadCount ω f center ≤ e}`,

as a `Finset` of functions on the cube. The body installs `classical` and
`Fintype.ofFinite K` so that the function space is a `Fintype` and the filter is
decidable.

**Remark.** The counting side of the argument works entirely with these balls: a
degree-`≤ D` candidate polynomial "explains" exactly the functions in the ball around
its own evaluation, so bounding `(rootCubeBall …).card` uniformly and multiplying by
the number of candidates gives the union bound.

**Used in.** The `hball` hypotheses of `rootCube_counting_obstruction` and
`no_low_degree_rootProd_approx_of_finite_counting`; bounded concretely by
`rootCubeBall_card_le_binomial` in `LowDegreeObstruction.lean`.
