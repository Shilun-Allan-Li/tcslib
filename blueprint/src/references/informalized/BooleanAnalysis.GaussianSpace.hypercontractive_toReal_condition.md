<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/Exponents.lean :: BooleanAnalysis.GaussianSpace.hypercontractive_toReal_condition -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Real form of the hypercontractive condition

**Claim.** When $1\leq p\leq q$ and $q$ is finite, the stated extended-real hypercontractive inequality implies the corresponding inequality for the real values of $p$ and $q$.

**Proof.** Because $p\leq q<\infty$, both exponents are finite. Apply the monotonicity of the extended-real-to-real map to the assumed inequality; the finite upper bound on the right ensures the subtraction there is finite as well. The real value of a product is the product of the real values, and the real values of $p-1$ and $q-1$ are respectively $p_{\mathbb R}-1$ and $q_{\mathbb R}-1$, since $p,q\geq1$. Also, the real value of the nonnegative extended-real number associated to $\rho^2$ is $\rho^2$. Translating the inequality through these identities yields $\rho^2(q_{\mathbb R}-1)\leq p_{\mathbb R}-1$.
