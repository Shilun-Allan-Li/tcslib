<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ImprovedKKL.lean :: FABL.exercise9_30_parameterized -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parameterized maximum-influence bound

**Claim.** For a Boolean function of positive variance and $0<\delta<1$, with $K=I/V$, the stated expression in $\delta$ and $K$ is at most the maximum coordinate influence.

**Proof.** Apply the bound in ratio form ($\texttt{exercise9\_30\_rho\_form}$), which gives the same inequality with $\rho=(1-\delta)/(1+\delta)$ and with the first factor written as $\rho^{-1/\delta}$. The hypotheses ensure $1-\delta$ and $1+\delta$ are nonzero, so $\rho^{-1}=(1+\delta)/(1-\delta)$. Rewriting reciprocals as inverse powers and substituting this identity yields exactly the claimed expression.

**Key facts.** `FABL.exercise9_30_rho_form`.
