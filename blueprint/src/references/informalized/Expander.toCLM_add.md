<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Expanders/Basic.lean :: Expander.toCLM_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Additivity of matrix operators

**Claim.** The continuous linear operator associated with the sum of two matrices is the sum of their associated operators.

**Proof.** Evaluate both operators at an arbitrary vector and coordinate. The matrix for the sum gives the coordinate $\sum_j(A_{ij}+B_{ij})v_j$. Distributing the finite sum over addition yields $\sum_jA_{ij}v_j+\sum_jB_{ij}v_j$, which is the corresponding coordinate of the sum of the two operator values. Since the coordinates agree for every vector, the operators are equal.
