<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/AlgebraicDegree.lean :: FABL.functionAlgebraicDegree_finset_prod_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree of a finite product

**Claim.** The algebraic degree of a finite pointwise product of functions on the binary cube is at most the sum of their algebraic degrees.

**Proof.** Proceed by induction on the finite index set. For the empty set, the product is the constant-one function, whose degree is zero (`functionAlgebraicDegree_one`), matching the empty sum. For the inductive step, write the product over the enlarged set as the new factor times the product over the previous set. The degree of a product is at most the sum of the two degrees (`functionAlgebraicDegree_mul_le_add`); combine this with the induction bound for the previous product to obtain the claimed sum bound.

**Key facts.** `FABL.functionAlgebraicDegree_one`, `FABL.functionAlgebraicDegree_mul_le_add`.
