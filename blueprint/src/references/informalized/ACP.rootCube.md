<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/SmolenskyAlgebra.lean :: rootCube -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The cube `{1, ω}^n`

**Definition.** For a field `K`, an element `ω : K` and `n : ℕ`,

`rootCube ω n = {x : Fin n → K // ∀ i, x i = 1 ∨ x i = ω}`,

the subtype of vectors each of whose coordinates is `1` or `ω`.

**Remark.** This is the domain on which the whole Smolensky argument runs: the
Boolean cube `{0,1}^n` is replaced by `{1, ω}^n` for `ω` a primitive `q`-th root of
unity in a field of characteristic `p`. Nothing forces `ω ≠ 1`, so the degenerate
case `ω = 1` gives a one-point cube; lemmas that need genuinely two points, or need
coordinatewise inverses, carry `hω0 : ω ≠ 0` or a nondegeneracy hypothesis
explicitly. `rootCubeFintype` supplies the `Fintype` instance when `K` is finite.

**Used in.** Everything in the `ModqRoadmap` section — `rootCubeBadCount`,
`rootCubeBall`, `rootCube_affine_inverse`, the multilinear-representative and
degree-splitting lemmas, and the counting obstruction.
