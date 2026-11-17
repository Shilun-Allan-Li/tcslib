<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/Comparison.lean :: BooleanAnalysis.Hypercontractivity.ComparisonAux.junta_threshold_parameters -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influence cutoff and noise parameters

**Claim.** Under the stated assumptions, set $\rho=\sqrt{\lambda}/3$ and $\tau=(\varepsilon/(2I))^2\rho^{2k}$. Then $0<\rho\le1$, $\tau>0$, $\sqrt{\tau}\,I=(\varepsilon/2)\rho^k$, and $I/\tau=(4I^3/\varepsilon^2)(9/\lambda)^k$.

**Proof.** Because $0<\lambda\le1/2$, its square root is positive and at most $1$, so $0<\rho\le1$. Positivity of $I$ and $\varepsilon$ then makes $\tau$ positive. Rewrite $\tau$ as $\bigl((\varepsilon/(2I))\rho^k\bigr)^2$. The quantity inside the square is nonnegative, so taking its square root and multiplying by $I$ gives $\sqrt{\tau}\,I=(\varepsilon/2)\rho^k$. Finally, $\rho^2=\lambda/9$, and hence $\rho^{2k}=(\lambda/9)^k$. Substitution into $I/\tau$ and simplification of positive factors gives $I/\tau=(4I^3/\varepsilon^2)(9/\lambda)^k$.
