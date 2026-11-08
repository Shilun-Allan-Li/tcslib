<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/Exponents.lean :: BooleanAnalysis.GaussianSpace.hypercontractive_exponents_of_nonzero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonzero correlation forces finite exponents

**Claim.** Under the stated exponent and correlation assumptions, $1<p$ and $q$ is finite.

**Proof.** Since $p<q\leq\infty$, $p$ is finite. If $q=\infty$, then $q-1=\infty$ and the nonzero factor $\rho^2$ makes the left side of the assumed inequality infinite, while $p-1$ is finite; this is impossible. Thus $q$ is finite. Converting the assumed extended-real inequality to real numbers gives $\rho^2(q_{\mathbb R}-1)\leq p_{\mathbb R}-1$ (`hypercontractive_toReal_condition`), where $p_{\mathbb R}$ and $q_{\mathbb R}$ denote the real values of the exponents. The inequalities $1\leq p<q$ imply $q_{\mathbb R}>1$. Since $\rho\ne0$, both $\rho^2$ and $q_{\mathbb R}-1$ are positive, so the displayed inequality forces $p_{\mathbb R}-1>0$. Hence $1<p$, and the finiteness of $q$ was already established.

**Key facts.** `BooleanAnalysis.GaussianSpace.hypercontractive_toReal_condition`.
