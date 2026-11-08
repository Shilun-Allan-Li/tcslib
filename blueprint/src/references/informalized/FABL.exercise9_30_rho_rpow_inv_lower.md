<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ImprovedKKL.lean :: FABL.exercise9_30_rho_rpow_inv_lower -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lower bound for a power of rho

**Claim.** For $0<\delta\le1/2$, with $\rho=(1-\delta)/(1+\delta)$, one has $\exp(-2-\delta^2)\le\rho^{1/\delta}$.

**Proof.** The logarithmic remainder is nonnegative on $[0,1/2]$ ($\texttt{exercise9\_30LogRemainder\_nonneg}$). Since $1-\delta$ and $1+\delta$ are positive, so is $\rho$, and $\log\rho=\log(1-\delta)-\log(1+\delta)$. The remainder inequality, after rearrangement and division by the positive $\delta$, gives $-2-\delta^2\le\log(\rho)/\delta$. Exponentiating preserves the inequality. For positive $\rho$, $\exp(\log(\rho)/\delta)=\rho^{1/\delta}$, giving the result.

**Key facts.** `FABL.exercise9_30LogRemainder_nonneg`.
