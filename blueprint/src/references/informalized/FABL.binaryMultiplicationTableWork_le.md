<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableFiniteFields.lean :: FABL.binaryMultiplicationTableWork_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Multiplication Table Work Bound

**Claim.** For every natural number $\ell$, the work required to construct the binary multiplication table of dimension $\ell$ is at most $9(\ell+1)^2 2^{2\ell}$.

**Proof.** Replace the table work by its exact formula, $2^{2\ell}\bigl(\ell(6\ell+2)+1\bigr)$ ($\texttt{binaryMultiplicationTableWork_eq}$). The multiplication routine's cost is $\ell(6\ell+2)$, and the arithmetic work bound implies this is at most $8(\ell+1)^2$: the multiplication cost is no larger than the maximum of the addition and multiplication costs, which is bounded by $8(\ell+1)^2$ ($\texttt{binaryArithmeticWork_le}$). Also $1\leq(\ell+1)^2$, so adding these estimates gives $\ell(6\ell+2)+1\leq9(\ell+1)^2$. Multiplying by the nonnegative factor $2^{2\ell}$ and rearranging the factors yields the claimed bound.

**Key facts.** `FABL.binaryMultiplicationTableWork_eq`, `FABL.binaryArithmeticWork_le`, `FABL.binaryMulModWork_eq`.
