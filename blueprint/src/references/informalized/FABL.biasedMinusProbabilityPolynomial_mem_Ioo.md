<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.biasedMinusProbabilityPolynomial_mem_Ioo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Strict interior range

**Claim.** For every $p\in(0,1)$, the biased minus-probability polynomial of a monotone, nonconstant Boolean function lies strictly between zero and one.

**Proof.** The endpoint theorem gives values zero and one at $p=0$ and $p=1$ (biasedMinusProbabilityPolynomial_endpoints). The polynomial is strictly increasing on $[0,1]$ (strictMonoOn_biasedMinusProbabilityPolynomial). Comparing any interior $p$ first with $0$ and then with $1$ therefore gives $0<F(p)<1$.

**Key facts.** `FABL.biasedMinusProbabilityPolynomial_endpoints`, `FABL.strictMonoOn_biasedMinusProbabilityPolynomial`.
