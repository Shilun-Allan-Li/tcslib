<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/FourierToF₂Polynomial.lean :: FABL.functionAlgebraicDegree_le_functionNumericalDegree_booleanRealEmbedding -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Algebraic degree bounded by numerical degree

**Claim.** For a function on the binary cube, the algebraic degree of its $\mathbb F_2$ encoding is at most the numerical degree of its Boolean real embedding.

**Proof.** Take the integer coefficient family for the numerical representation of the Boolean real embedding. Reducing each coefficient modulo two gives the algebraic normal form coefficients (`booleanNumericalCoeffInt_cast_f₂_eq_anfCoeff`). For any integer coefficient family, the degree after reduction modulo two is at most the real numerical degree of the same coefficients (`algebraicDegree_intCastModTwo_le_numericalDegree`). Finally, the real numerical coefficients of the Boolean embedding are exactly those integer coefficients viewed in $\mathbb R$ (`numericalCoeff_booleanRealEmbedding_eq_intCast`). Chaining these identifications and the degree bound proves the result.

**Key facts.** `FABL.booleanNumericalCoeffInt_cast_f₂_eq_anfCoeff`, `FABL.algebraicDegree_intCastModTwo_le_numericalDegree`, `FABL.numericalCoeff_booleanRealEmbedding_eq_intCast`.
