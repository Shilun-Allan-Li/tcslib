<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/AlmostKWiseAlgorithm.lean :: FABL.almostKWiseMatrixVecMulWork_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Matrix-vector multiplication work bound

**Claim.** For the given almost-wise input, the matrix-vector multiplication work is at most $9(s+1)^3$.

**Proof.** Write $R=s+1$. The scale satisfies $R\ge1$, the output dimension satisfies $n\le R$ ($\texttt{AlmostKWiseInput.n\_le\_scale}$), and the row count is at most $4R^2$ ($\texttt{AlmostKWiseInput.rowCount\_le\_four\_scale\_sq$). The traversal work equals the number of columns times the step cost, namely $n(2\,\mathrm{rowCount}+1)$ ($\texttt{executableMatrixVecMulWork\_eq$). These bounds give $n(2\,\mathrm{rowCount}+1)\le R(8R^2+1)\le R(9R^2)=9R^3$, using $R^2\ge1$ for the middle inequality.

**Key facts.** `FABL.AlmostKWiseInput.n_le_scale`, `FABL.AlmostKWiseInput.rowCount_le_four_scale_sq`, `FABL.executableMatrixVecMulWork_eq`.
