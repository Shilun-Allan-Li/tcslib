<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/SmolenskyAlgebra.lean :: rootCubeFunctionBadCount -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Hamming distance between two functions on `{1, ω}^n`

**Definition.** For finite `K` and `f g : rootCube ω n → K`,

`rootCubeFunctionBadCount ω f g = #{x : rootCube ω n | g x ≠ f x}`,

the number of cube points where `f` and `g` differ. `classical` supplies the filter's
decidability.

**Remark.** Symmetric in the two arguments as a number, but the argument order is
chosen so that the second slot is the "center": this matches
`rootCubeBadCount`, where the polynomial is compared against the target function, and
lets `rootCubeBall` be defined by fixing the second argument.

**Used in.** `rootCubeBall`, and unfolded together with it inside
`rootCube_counting_obstruction` to reach the plain-`Finset.filter` form that
`finite_cover_by_hamming_balls_card_bound` expects.
