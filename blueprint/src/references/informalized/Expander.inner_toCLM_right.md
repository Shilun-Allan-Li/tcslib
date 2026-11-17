<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Expanders/Basic.lean :: Expander.inner_toCLM_right -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Symmetry of the Matrix Operator

**Claim.** For a symmetric real matrix $A$ and vectors $x,y$, one has $\langle Ax,y\rangle=\langle x,Ay\rangle$.

**Proof.** Write each inner product as a sum over coordinates, and expand each matrix-vector product coordinate as $\sum_j A_{ij}v_j$ (`toCLM_apply_coord`). Distributing the sums and exchanging their order expresses both sides as double sums. In the left-hand sum, symmetry gives $A_{ji}=A_{ij}$; commutativity of multiplication then identifies each summand with the corresponding summand on the right. Thus the inner products agree.

**Key facts.** `Expander.inner_eq_sum`, `Expander.toCLM_apply_coord`.
