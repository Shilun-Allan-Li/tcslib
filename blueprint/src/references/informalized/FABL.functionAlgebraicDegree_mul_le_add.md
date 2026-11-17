<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/AlgebraicDegree.lean :: FABL.functionAlgebraicDegree_mul_le_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree of a product

**Claim.** The algebraic degree of the pointwise product of two Boolean functions is at most the sum of their algebraic degrees.

**Proof.** The algebraic normal form of a pointwise product is the product of the two algebraic normal forms (`anfCoeff_mul`). The degree bound for multiplying algebraic normal forms (`algebraicDegree_anfMul_le_add`) then gives that the degree of this product is at most the sum of the degrees of the two factors, as required.

**Key facts.** `FABL.anfCoeff_mul`, `FABL.algebraicDegree_anfMul_le_add`.
