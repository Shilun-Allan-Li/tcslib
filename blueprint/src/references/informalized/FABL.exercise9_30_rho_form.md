<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ImprovedKKL.lean :: FABL.exercise9_30_rho_form -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lower bound for maximum influence

**Claim.** For a Boolean function of positive variance and $0<\delta<1$, writing $\rho=(1-\delta)/(1+\delta)$ and $K=I(f)/\operatorname{Var}(f)$, the stated product of powers of $\rho$ and $K$ is at most the maximum coordinate influence.

**Proof.** The variance bound by total influence ($\texttt{variance\_le\_totalInfluence}$) implies $K\ge1$, so $K>0$. The ratio parameter satisfies $0<\rho<1$ ($\texttt{exercise9\_30Rho\_mem\_Ioc}$). Recombine the powers in the left side: using $\rho^{-\delta^{-1}}=\rho^{ -\delta^{-1}}$ and $K^{-1}=1/K$, their product is $(\rho^{K-1}/K)^{\delta^{-1}}$. This identity follows from the addition and multiplication laws for real powers, with positivity of $\rho$ and nonnegativity of the relevant bases. The compact maximum-influence bound ($\texttt{exercise9\_30\_compact}$) bounds this final expression by the maximum coordinate influence.

**Key facts.** `FABL.variance_le_totalInfluence`, `FABL.exercise9_30Rho_mem_Ioc`, `FABL.exercise9_30_compact`.
