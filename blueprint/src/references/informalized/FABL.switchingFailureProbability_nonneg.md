<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.switchingFailureProbability_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegative switching failure

**Claim.** For a sign-valued Boolean function and $0\le\delta\le1$, the switching-failure probability at threshold $k$ is nonnegative.

**Proof.** Expand the probability as a finite sum over subsets $J\subseteq[n]$. Each summand is the product of the random-subset weight and the average of the switching-failure indicator over fixed signs. The weight is nonnegative by the nonnegativity of the powers of $\delta$ and $1-\delta$ ($\texttt{deltaRandomSubsetWeight_nonneg}$), and the average is nonnegative because the indicator takes only the values $0$ and $1$ ($\texttt{switchingFailureIndicator_nonneg}$). Thus every summand is nonnegative, so their sum is nonnegative.

**Key facts.** `FABL.deltaRandomSubsetWeight_nonneg`, `FABL.switchingFailureIndicator_nonneg`.
