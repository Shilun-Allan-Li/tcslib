<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/OneBitHypercontractivity.lean :: FABL.meanZero_qq_hypercontractive_real -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Contraction under mean-zero scaling

**Claim.** If $X$ has mean zero, then for $q\geq1$, $0\leq\rho\leq1$, and real $a,b$, the $q$-norm of $a+\rho bX$ is at most that of $a+bX$.

**Proof.** Set $F=a+bX$. By linearity of expectation and the assumption that $X$ has mean zero, $F$ has mean $a$. The norm dominates the absolute value of the mean ($\texttt{FABL.abs_expect_le_uniformLpNorm}$), so $|a|\leq\|F\|_q$. Rewrite $a+\rho bX=(1-\rho)a+\rho F$. The triangle inequality for the uniform $q$-norm ($\texttt{FABL.uniformLpNorm_add_le}$), together with its scaling rule ($\texttt{FABL.uniformLpNorm_const_mul}$), bounds its norm by $(1-\rho)|a|+\rho\|F\|_q$. Since both coefficients are nonnegative, replacing $|a|$ by its upper bound $\|F\|_q$ gives exactly $\|F\|_q$.

**Key facts.** `FABL.abs_expect_le_uniformLpNorm`, `FABL.uniformLpNorm_add_le`, `FABL.uniformLpNorm_const_mul`.
