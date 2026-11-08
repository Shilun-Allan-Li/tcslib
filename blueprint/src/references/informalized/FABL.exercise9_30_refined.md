<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ImprovedKKL.lean :: FABL.exercise9_30_refined -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Refined maximum-influence bound

**Claim.** For a Boolean function of positive variance, setting $K=I/V$, the stated exponential and power expression is at most its maximum coordinate influence.

**Proof.** Let $R=K^{1/3}$, $\delta=1/(2R)$, and $\rho=(1-\delta)/(1+\delta)$. First, the variance bound by total influence ($\texttt{variance\_le\_totalInfluence}$) gives $K\ge1$, hence $R\ge1$ and $0<\delta\le1/2$. Also $R^3=K$ and $\delta^{-1}=2R$. The ratio parameter lies in $(0,1)$ ($\texttt{exercise9\_30Rho\_mem\_Ioc}$), so its real powers can be compared using the lower bound $\exp(-2-\delta^2)\le\rho^{1/\delta}$ ($\texttt{exercise9\_30\_rho\_rpow\_inv\_lower}$). Raising this inequality to the nonnegative power $K-1$ gives $\exp((-2-\delta^2)(K-1))\le\rho^{(K-1)2R}$. Since $\delta^2(K-1)\le R/4$, the exponent on the left is at least $-2K+2-R/4$, and therefore $\exp(-2K+2-R/4)\le\rho^{(K-1)2R}$. Multiply by the nonnegative factor $K^{-2R}$. The compact maximum-influence bound ($\texttt{exercise9\_30\_compact}$), with $\delta^{-1}=2R$, bounds $\rho^{(K-1)2R}K^{-2R}$ by the maximum influence. Finally, combine the exponential factors $\exp(-2K)\exp(2)\exp(-R/4)$ and use $R=K^{1/3}$ to obtain the claim.

**Key facts.** `FABL.variance_le_totalInfluence`, `FABL.exercise9_30Rho_mem_Ioc`, `FABL.exercise9_30_rho_rpow_inv_lower`, `FABL.exercise9_30_compact`.
