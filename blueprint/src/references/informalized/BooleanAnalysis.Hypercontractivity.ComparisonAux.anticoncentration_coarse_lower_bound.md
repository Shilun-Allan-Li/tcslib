<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/Comparison.lean :: BooleanAnalysis.Hypercontractivity.ComparisonAux.anticoncentration_coarse_lower_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coarse anticoncentration coefficient

**Claim.** For every real $\lambda>0$ and positive integer $k$, $(15/\lambda)^{-k}\le \frac14(e^2/(2\lambda))^{-k}$, where the exponents denote real powers with exponent $-k$.

**Proof.** Put $A=e^2/(2\lambda)$ and $B=15/\lambda$, both positive. The elementary estimate $e^2\le15/2$ implies $A/B=e^2/30\le1/4$. Since $0<A/B\le1$ and $k\ge1$, raising this ratio to the power $k$ gives $(A/B)^k\le A/B\le1/4$. Rewriting this as $A^k\le B^k/4$ and dividing by the positive quantity $A^kB^k$ yields $B^{-k}\le (1/4)A^{-k}$, as required.
