<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/AlgebraicDegree.lean :: FABL.anfCoeff_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coefficients of a product

**Claim.** The algebraic normal form coefficient of the pointwise product $fg$ at each set is the sum over pairs of sets whose union is that set, of the products of the corresponding coefficients of $f$ and $g$.

**Proof.** Apply the evaluation map to both coefficient families. Evaluating the coefficients of $fg$ recovers $fg$ (`anfEval_anfCoeff`). Evaluating the coefficient product formula gives the product of the evaluations of the two families (`anfEval_anfMul`), and each evaluation recovers its original function (`anfEval_anfCoeff`). Thus the two families have the same evaluation at every input. Injectivity of evaluation (`anfEval_injective`) implies that the coefficient families agree.

**Key facts.** `FABL.anfEval_anfCoeff`, `FABL.anfEval_anfMul`, `FABL.anfEval_injective`.
