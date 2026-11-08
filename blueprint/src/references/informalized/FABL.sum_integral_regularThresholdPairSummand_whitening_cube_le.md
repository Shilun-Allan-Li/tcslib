<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/RegularThresholdNoiseStability.lean :: FABL.sum_integral_regularThresholdPairSummand_whitening_cube_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Whitened Summand Bound

**Claim.** The sum of the expected cubed norms of the whitened correlated sign summands is at most $4\varepsilon/\sqrt{1-\rho^2}$.

**Proof.** Since $-1<\rho<1$, we have $(1+\rho)(1-\rho)>0$, so $\sqrt{1-\rho^2}>0$. For each coordinate $i$, the single-coordinate whitening estimate (\texttt{FABL.integral_regularThresholdPairSummand_whitening_cube_le}) bounds its expected cubed norm by $4|a_i|^3/\sqrt{1-\rho^2}$. Regularity gives $|a_i|\le\varepsilon$; multiplying by $a_i^2\ge0$ yields $|a_i|^3\le\varepsilon a_i^2$. Summing these inequalities and using $\sum_i a_i^2=1$ gives the claimed bound.

**Key facts.** `FABL.integral_regularThresholdPairSummand_whitening_cube_le`.
