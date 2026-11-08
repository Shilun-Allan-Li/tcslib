<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdComplements.lean :: FABL.biasedMinusProbabilityPolynomial_le_refined_rpow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Refined power bound

**Claim.** If $0<r<1$, $0<p\le p_a<1$, and the polynomial at $p_a$ is at most $r$, then its value at $p$ is at most $r(p/p_a)^{1-r}$.

**Proof.** The monotonicity theorem for the refined logarithmic ratio (refinedLowerLogRatio_monotoneOn) compares its values at $p$ and $p_a$. Using the assumed bound at $p_a$ and taking logarithms, which is valid because the polynomial lies strictly between zero and one at interior parameters (biasedMinusProbabilityPolynomial_mem_Ioo), this comparison yields $\log F(p)\le\log r+(1-r)(\log p-\log p_a)$. Exponentiating gives $F(p)\le r(p/p_a)^{1-r}$.

**Key facts.** `FABL.refinedLowerLogRatio_monotoneOn`, `FABL.biasedMinusProbabilityPolynomial_mem_Ioo`.
