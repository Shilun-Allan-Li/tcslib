<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/LearningConsequencesResources.lean :: FABL.cubicSampleExpression_le_fixed_power -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cubic Sample Expression Bound

**Claim.** If $M\le A(n+1)^E$ and $(1/\varepsilon)^2\le Q^2$ for positive rational $\varepsilon$, then $640M^3/\varepsilon^2\le640A^3Q^2(n+1)^{3E}$.

**Proof.** Cubing $M\le A(n+1)^E$ preserves the inequality, so $M^3\le A^3(n+1)^{3E}$. Since $\varepsilon>0$, rewrite $1/\varepsilon^2$ as $(1/\varepsilon)^2$ and use its assumed upper bound $Q^2$. Multiplying the two nonnegative bounds and then multiplying by $640$ yields $640A^3Q^2(n+1)^{3E}$.
