<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/SmolenskyAlgebra.lean :: rootCube_coord_ne_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Coordinates on `{1, ω}^n` are nonzero

**Claim.** If `ω ≠ 0` then every coordinate of every point of the cube
`rootCube ω n = {x : Fin n → K // ∀ i, x i = 1 ∨ x i = ω}` is nonzero: for `x : rootCube ω n`
and `i : Fin n`, `x.1 i ≠ 0`.

**Proof.** `rcases x.2 i` on the membership disjunction supplied by the subtype.

* If `x.1 i = 1`, then `simp [hx]` closes the goal (`1 ≠ 0` in a field).
* If `x.1 i = ω`, then `simpa [hx] using hω0` is exactly the hypothesis.

**Used in.** `rootCube_top_mul_compl_inverse`, where coordinatewise inverses must exist.
