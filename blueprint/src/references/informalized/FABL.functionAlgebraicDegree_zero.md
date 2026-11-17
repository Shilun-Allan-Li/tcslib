<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/AlgebraicDegree.lean :: FABL.functionAlgebraicDegree_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree of the zero function

**Claim.** The zero function on the Boolean cube has algebraic degree $0$.

**Proof.** The algebraic-normal-form coefficients of the zero function all vanish (`anfCoeff_zero`). A coefficient family that is identically zero has algebraic degree zero (`algebraicDegree_zero`); therefore the zero function has algebraic degree zero.

**Key facts.** `FABL.anfCoeff_zero`, `FABL.algebraicDegree_zero`.
