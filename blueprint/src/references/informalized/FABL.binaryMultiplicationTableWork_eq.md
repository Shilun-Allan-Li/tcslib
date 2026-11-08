<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableFiniteFields.lean :: FABL.binaryMultiplicationTableWork_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Multiplication Table Work

**Claim.** For every natural number $\ell$, the work assigned to the multiplication table on binary vectors of length $\ell$ is $2^{2\ell}\bigl(\ell(6\ell+2)+1\bigr)$.

**Proof.** The table work is the operation-table work with the multiplication routine's cost. The operation-table formula says that on all ordered pairs of binary vectors, the traversal performs $2^{2\ell}$ steps, each costing the operation work plus one ($\texttt{binaryOperationTableWork_eq}$). Substituting the multiplication routine's cost $\ell(6\ell+2)$ ($\texttt{binaryMulModWork_eq}$) gives the stated formula.

**Key facts.** `FABL.binaryOperationTableWork_eq`, `FABL.binaryMulModWork_eq`.
