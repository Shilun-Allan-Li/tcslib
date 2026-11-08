<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/PrivateCoinApproximation.lean :: CommunicationComplexity.Internal.weighted_sum_approx -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Weighted Sum Approximation

**Claim.** If every subset sum of $p$ is at most the corresponding subset sum of $q$ plus $\delta$, then every weighted sum with weights between $0$ and $1$ obeys the same error bound.

**Proof.** Let $A^+=\{a:q(a)<p(a)\}$. On its complement, $p(a)-q(a)\le 0$, so nonnegativity of $g(a)$ gives $(p(a)-q(a))g(a)\le 0$. On $A^+$, the difference $p(a)-q(a)$ is positive and $g(a)\le 1$, hence $(p(a)-q(a))g(a)\le p(a)-q(a)$. Summing over these two parts, the total weighted difference is at most $\sum_{a\in A^+}(p(a)-q(a))$. Applying the subset hypothesis to $A^+$ bounds this last sum by $\delta$. Finally, distributing the finite sum over subtraction identifies the weighted difference with $\sum_a p(a)g(a)-\sum_a q(a)g(a)$, yielding the result.
