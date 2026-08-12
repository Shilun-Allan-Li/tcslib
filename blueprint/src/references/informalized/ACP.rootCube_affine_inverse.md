<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/SmolenskyAlgebra.lean :: rootCube_affine_inverse -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# On `{1, ω}^n` the affine map `1 + ω⁻¹ - ω⁻¹ t` is inversion

**Claim.** Let `ω ≠ 0`, `x : rootCube ω n` and `i : Fin n`. Then

`1 + ω⁻¹ - ω⁻¹ * x.1 i = (x.1 i)⁻¹`.

**Proof.** Case split on the cube membership `x.2 i`, i.e. `rcases x.2 i with hx | hx`.

- If `x.1 i = 1`: the left side is `1 + ω⁻¹ - ω⁻¹ = 1 = 1⁻¹`, closed by `simp [hx]`.
- If `x.1 i = ω`: `ω⁻¹ * ω = 1` since `ω ≠ 0`, so the left side is
  `1 + ω⁻¹ - 1 = ω⁻¹`, closed by `simp [hx, hω0]`.

**Remark.** This is the identity that makes the degree-splitting step legitimate:
the substitution `x i ↦ 1 + ω⁻¹ - ω⁻¹ x i` appearing in the split
`F(x) = F₁(x) + (∏ i, x i) · F₂(…)` is polynomial (degree 1 in each coordinate) yet
acts on the cube as coordinatewise inversion, which is what the monomial-complement
cancellation needs.

**Used in.** `rootCube_top_mul_compl_inverse`'s companion rewriting steps and the two
`split_multilinear_at_half_degree…` proofs (lines 656 and 859).
