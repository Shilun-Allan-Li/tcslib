<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/Comparison.lean :: BooleanAnalysis.Hypercontractivity.ComparisonAux.junta_polynomial_absorption -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Absorbing polynomial factors

**Claim.** If $0<\lambda\le1/2$, $0<\varepsilon\le1$, $\varepsilon\le I$, and $k\le3I/\varepsilon$, then $\frac{4I^3}{\varepsilon^2}(9/\lambda)^k\le(1/\lambda)^{100I/\varepsilon}$.

**Proof.** Set $t=I/\varepsilon$ and $L=\log(1/\lambda)$. Then $t\ge1$. The logarithmic parameter bounds (`kkl_log_parameters`) give $L\ge1/2$ and $\log(9/\lambda)\le5L$. First, using $\varepsilon\le1$ and $t\ge1$, we have $4I^3/\varepsilon^2=4\varepsilon t^3\le4t^3\le(2t)^3\le e^{3t}$; the last inequality uses $2t\le e^t$. Next, $k\le3t$ and $\log(9/\lambda)\ge0$ imply $(9/\lambda)^k\le e^{15tL}$. Multiplication bounds the left side by $e^{3t+15tL}$. Since $L\ge1/2$, $3t+15tL\le100tL$, so this is at most $e^{100tL}=(1/\lambda)^{100I/\varepsilon}$.

**Key facts.** `BooleanAnalysis.Hypercontractivity.ComparisonAux.kkl_log_parameters`.
