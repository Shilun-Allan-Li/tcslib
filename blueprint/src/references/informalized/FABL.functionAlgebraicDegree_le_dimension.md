<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/AlgebraicDegree.lean :: FABL.functionAlgebraicDegree_le_dimension -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dimension bound for algebraic degree

**Claim.** Every function on the $n$-dimensional binary cube has algebraic degree at most $n$.

**Proof.** The degree of a function is the degree of its algebraic normal form, whose coefficients form a family indexed by subsets of the $n$ coordinates. The algebraic degree of any such coefficient family is at most the dimension (`algebraicDegree_le_dimension`). Applying this bound to the algebraic normal form coefficients proves the claim.

**Key facts.** `FABL.algebraicDegree_le_dimension`.
