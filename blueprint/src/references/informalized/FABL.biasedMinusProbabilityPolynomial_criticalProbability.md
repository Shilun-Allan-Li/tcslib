<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedAnalysis.lean :: FABL.biasedMinusProbabilityPolynomial_criticalProbability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Critical parameter identity

**Claim.** For a monotone, nonconstant Boolean function, the biased minus-probability polynomial at its critical probability equals $1/2$.

**Proof.** The existence-and-uniqueness theorem supplies a unique parameter $p$ in $(0,1)$ for which the polynomial equals $1/2$. The critical probability is defined to be the parameter selected from this witness. The witness’s second property therefore gives the claimed equality.

**Key facts.** `FABL.existsUnique_criticalProbability`.
