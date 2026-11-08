<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/RegularThresholdNoiseStability.lean :: FABL.exercise5_33a -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Factorization of the inverse correlation matrix

**Claim.** For $-1<\rho<1$, the inverse of $R=\begin{pmatrix}1&\rho\\\rho&1\end{pmatrix}$ equals the displayed product of three matrices.

**Proof.** The inequalities on $\rho$ imply $1-\rho>0$ and $1+\rho>0$, so $1-\rho^2=(1-\rho)(1+\rho)\ne0$. It suffices to verify that the proposed product is a left inverse of $R$. Multiplying the three displayed factors and then multiplying by $R$ gives the identity matrix: entrywise, the diagonal entries simplify to $1$ and the off-diagonal entries to $0$, using the nonvanishing of $1-\rho^2$. A left inverse of a square matrix is its inverse, proving the factorization.
