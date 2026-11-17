<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedAnalysis.lean :: FABL.existsUnique_criticalProbability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unique Critical Probability

**Claim.** For a monotone, nonconstant Boolean function, there is a unique probability $p\in(0,1)$ at which its biased minus-probability polynomial equals $1/2$.

**Proof.** The polynomial is continuous, and its endpoint values are $0$ and $1$ (`biasedMinusProbabilityPolynomial_endpoints`, `continuous_biasedMinusProbabilityPolynomial`). The intermediate value theorem therefore gives some $p\in[0,1]$ where it equals $1/2$. The endpoint values show that this $p$ cannot be $0$ or $1$, so it lies in $(0,1)$. Finally, the polynomial is strictly increasing on $[0,1]$ (`strictMonoOn_biasedMinusProbabilityPolynomial`), which makes two distinct solutions there impossible. Hence the solution in $(0,1)$ is unique.

**Key facts.** `FABL.biasedMinusProbabilityPolynomial_endpoints`, `FABL.continuous_biasedMinusProbabilityPolynomial`, `FABL.strictMonoOn_biasedMinusProbabilityPolynomial`.
