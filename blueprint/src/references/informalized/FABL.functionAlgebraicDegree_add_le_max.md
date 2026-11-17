<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/AlgebraicDegree.lean :: FABL.functionAlgebraicDegree_add_le_max -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree of a sum

**Claim.** The algebraic degree of the pointwise sum of two Boolean functions is at most the maximum of their algebraic degrees.

**Proof.** The ANF coefficient of the sum, at each subset of coordinates, is the sum of the two corresponding ANF coefficients (`FABL.anfCoeff_add`). The algebraic degree of a coefficient function formed by adding two coefficient functions is at most the maximum of their degrees (`FABL.algebraicDegree_add_le_max`). Applying this fact to the two ANF coefficient functions proves the bound.

**Key facts.** `FABL.anfCoeff_add`, `FABL.algebraicDegree_add_le_max`.
