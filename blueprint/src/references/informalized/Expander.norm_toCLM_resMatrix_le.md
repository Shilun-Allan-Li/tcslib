<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Expanders/Walks.lean :: Expander.norm_toCLM_resMatrix_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Norm bound for a restricted matrix

**Claim.** Under the stated stochasticity and spectral hypotheses, restricting $A$ to rows in $B$ gives $\|A_Bx\|\le ((1-\lambda)\sqrt{\beta}+\lambda)\|x\|$.

**Proof.** 1. By the decomposition theorem (\(\texttt{Expander.exists\_decomposition}\)), write $A=(1-\lambda)J+\lambda C$, where $J$ is the uniform matrix and $\|C\|\le1$. Row restriction preserves this decomposition because it acts entry by entry on each row. Linearity of the matrix operator (\(\texttt{Expander.toCLM\_add}\) and \(\texttt{Expander.toCLM\_smul}\)) therefore expresses $A_Bx$ as the same weighted sum of $J_Bx$ and $C_Bx$.\n\n2. Restricting rows cannot increase the norm of a matrix–vector product: it retains some coordinates and sets the others to zero. In coordinates, the matrix action is the row sum $\sum_j M_{ij}y_j$ (\(\texttt{Expander.toCLM\_apply\_coord}\)), and the restricted entries have the stated retain-or-zero form (\(\texttt{Expander.resMatrix\_apply}\)). Thus $\|C_By\|\le\|Cy\|\le\|C\|\|y\|\le\|y\|$.\n\n3. Every retained coordinate of $J_By$ equals $(1/n)\sum_j y_j$. Consequently, $\|J_By\|^2=|B|(1/n)^2(\sum_j y_j)^2$. The size bound gives $|B|\le\beta n$, while Cauchy–Schwarz gives $(\sum_j y_j)^2\le n\sum_j y_j^2$. Combining these inequalities yields $\|J_By\|^2\le\beta\|y\|^2$, hence $\|J_By\|\le\sqrt{\beta}\|y\|$.\n\n4. Apply the triangle inequality to the decomposition of $A_Bx$. Since $0\le\lambda\le1$, both coefficients are nonnegative, so the preceding bounds give $\|A_Bx\|\le(1-\lambda)\sqrt{\beta}\|x\|+\lambda\|x\|$, which is the asserted estimate.

**Key facts.** `Expander.exists_decomposition`, `Expander.toCLM_apply_coord`, `Expander.resMatrix_apply`, `Expander.toCLM_add`, `Expander.toCLM_smul`.
