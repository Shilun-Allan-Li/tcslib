<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Applications/KKL/Threshold.lean :: BooleanAnalysis.Hypercontractivity.linearThreshold_junta_size_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Junta Size Estimate

**Claim.** Under the stated bounds on $B,\varepsilon,\eta$, and $k$, the quantity $1/(\varepsilon(\eta/(2+\eta))^k)^{1+\eta}$ is at most $(1/\eta)^{200B/\varepsilon^2}$.

**Proof.** Set $\rho=\eta/(2+\eta)$ and $I=B/\varepsilon$. The hypotheses imply $0<\rho\leq1$, $I\geq1$, and $I/\varepsilon=B/\varepsilon^2$. First bound the left side by replacing its exponent $1+\eta\leq2$ with $2$: since $0<\varepsilon\rho^k\leq1$, its reciprocal is at least $1$. This gives $1/\varepsilon^2\,(1/\rho^2)^k$. As $\eta\leq1/2$, we have $2+\eta\leq3$, hence $1/\rho^2\leq9/\eta^2$. Also $1\leq I^3$, so $1/\varepsilon^2\leq4I^3/\varepsilon^2$. Consequently the expression is at most $(4I^3/\varepsilon^2)(9/\eta^2)^k$.

Now use the polynomial absorption estimate with $\lambda=\eta^2$: here $0<\lambda\leq1/2$, $\varepsilon\leq I$, and the cutoff hypothesis gives $k\leq3(I/\varepsilon)$. It bounds this last product by $(1/\eta^2)^{100I/\varepsilon}$. Rewrite that power as $(1/\eta)^{200I/\varepsilon}$ and use $I/\varepsilon=B/\varepsilon^2$ to obtain the asserted upper bound.

**Key facts.** `BooleanAnalysis.Hypercontractivity.ComparisonAux.junta_polynomial_absorption`.
