<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/AlgebraicDegree.lean :: FABL.algebraicDegree_add_le_max -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree of a sum

**Claim.** The algebraic degree of the pointwise sum of two coefficient functions over the field with two elements is at most the maximum of their algebraic degrees.

**Proof.** Use the support characterization of degree ($\texttt{algebraicDegree_le_iff}$): it suffices to bound the cardinality of every subset whose summed coefficient is nonzero. If both original coefficients on that subset were zero, their sum would be zero, so at least one original coefficient is nonzero. The subset's cardinality is therefore at most the degree of that coefficient function, and hence at most the maximum of the two degrees.

**Key facts.** `FABL.algebraicDegree_le_iff`.
