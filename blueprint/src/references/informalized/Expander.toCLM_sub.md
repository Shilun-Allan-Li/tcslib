<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Expanders/Basic.lean :: Expander.toCLM_sub -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Subtraction of Matrix Operators

**Claim.** For real matrices $A$ and $B$, the operator associated with $A-B$ equals the operator associated with $A$ minus the operator associated with $B$.

**Proof.** Compare the two operators on an arbitrary vector and then at each coordinate. The coordinate on the left is $\sum_j (A_{ij}-B_{ij})v_j$; the coordinate on the right is $\sum_j A_{ij}v_j-\sum_j B_{ij}v_j$. Distributing subtraction across the finite sum identifies these expressions, because $(A_{ij}-B_{ij})v_j=A_{ij}v_j-B_{ij}v_j$. Hence the operators are equal.
