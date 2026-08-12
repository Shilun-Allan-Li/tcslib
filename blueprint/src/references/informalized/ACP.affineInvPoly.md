<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/SmolenskyAlgebra.lean :: affineInvPoly -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The affine coordinate transform `x ↦ 1 + ω⁻¹ - ω⁻¹ x` as a polynomial

**Definition.** For a field `K`, `ω : K`, and `i : Fin n`,

`affineInvPoly ω i := MvPolynomial.C (1 + ω⁻¹) + MvPolynomial.C (-ω⁻¹) * MvPolynomial.X i`

in `MvPolynomial (Fin n) K`. It is the degree-one polynomial in the single
variable `X i` whose value at `x` is `1 + ω⁻¹ - ω⁻¹ * x i`.

**Remark.** On the two-point set `{1, ω}` with `ω ≠ 0` this affine map is exactly
inversion `x ↦ x⁻¹` (see `rootCube_affine_inverse`), which is why it is the
substitution used in the Smolensky split step; written this way it is an honest
polynomial, so degree bounds apply to it. No hypothesis on `ω` is imposed here —
for `ω = 0` the definition still makes sense in Lean (`0⁻¹ = 0`) and reduces to
the constant `1`.

**Used in.** `affineInvPoly_eval`, `affineInvPoly_totalDegree_le_one`, and
`affineSquarefreeMonomial`.
