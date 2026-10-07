<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/SmolenskyAlgebra.lean :: affineInvPoly_totalDegree_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The affine inverse polynomial has total degree at most one

**Claim.** For a field `K`, `ω : K`, and `i : Fin n`,
`(affineInvPoly ω i).totalDegree ≤ 1`.

**Proof.** `unfold affineInvPoly`, then a two-step `calc`.

1. `MvPolynomial.totalDegree_add` bounds the degree of the sum
   `C (1 + ω⁻¹) + C (-ω⁻¹) * X i` by the max of the two summands' degrees.
2. `max_le` splits into the two summands:
   - the constant term has degree `≤ 1`, shown by another
     `MvPolynomial.totalDegree_add` step on `1 + C ω⁻¹` finished by `simp`, and
     transported to `C (1 + ω⁻¹)` by `simpa`;
   - the linear term satisfies
     `(C (-ω⁻¹) * X i).totalDegree ≤ (C (-ω⁻¹)).totalDegree + (X i).totalDegree ≤ 0 + 1 = 1`
     by `MvPolynomial.totalDegree_mul` and `simp`.

**Remark.** Deliberately granular: it exists so that
`affineSquarefreeMonomial_totalDegree_le_card` can bound a product of `s.card`
such factors termwise. The bound is `≤ 1`, not `= 1`, since `ω⁻¹` may vanish.
