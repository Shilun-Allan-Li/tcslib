<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Expanders/Basic.lean :: Expander.toCLM_smul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Homogeneity of Matrix Operators

**Claim.** For every real scalar $c$ and real matrix $A$, the operator associated with $cA$ equals $c$ times the operator associated with $A$.

**Proof.** It suffices to compare the two operators on an arbitrary vector and then compare each coordinate. At coordinate $i$, the first operator gives $\sum_j (cA_{ij})v_j$, while the second gives $c\sum_j A_{ij}v_j$. Distributing $c$ across the finite sum makes these expressions equal, since each summand satisfies $(cA_{ij})v_j=c(A_{ij}v_j)$. Thus the operators agree on every vector.
