<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/MatrixExponentSolver.lean :: FABL.matrixExponentJuntaCeilSolverExponent_le_cutoff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Solver Exponent Ceiling Bound

**Claim.** If $c=\lceil\omega k/(\omega+1)\rceil$, then $\lceil\omega(k-c)\rceil\le c$, where $k-c$ is truncated subtraction on natural numbers.

**Proof.** The ceiling characterization reduces the claim to showing that the solver exponent is at most $c$. The upstream bound `matrixExponentJuntaSolverExponent_le_cutoff` gives precisely this inequality. To identify its solver exponent with the expression here, use `matrixExponentJuntaCutoff_le_k`: it ensures $c\le k$, so casting the natural subtraction $k-c$ to the rationals gives $k-c$. Thus the solver exponent is $\omega(k-c)$, and its ceiling is at most the cutoff $c$.

**Key facts.** `FABL.matrixExponentJuntaCutoff_le_k`, `FABL.matrixExponentJuntaSolverExponent_le_cutoff`.
