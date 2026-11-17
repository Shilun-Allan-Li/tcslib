<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/PolynomialThresholdInfluence.lean :: FABL.polynomialThresholdNoiseModulus_tendsto_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Vanishing Noise Modulus

**Claim.** Fix a natural number $k$. For $0\leq\delta\leq\tfrac12$, define $\omega_k(\delta)=\min\{1,3\delta^{2^{-k}}\}$. As positive $\delta$ in this interval tends to $0$, $\omega_k(\delta)$ tends to $0$.

**Proof.** Write $\beta=2^{-k}$; the positivity of the noise exponent gives $\beta>0$. The function $x\mapsto x^\beta$ is continuous at $0$ with value $0$, so as $\delta$ tends to $0$ within the specified parameter set, $\delta^\beta$ tends to $0$. Multiplication by $3$ preserves this limit. The constant function with value $1$ tends to $1$, and the minimum of two convergent real-valued functions tends to the minimum of their limits. Thus $\min\{1,3\delta^\beta\}$ tends to $\min\{1,0\}=0$.

**Key facts.** `FABL.polynomialThresholdNoiseExponent_pos`.
