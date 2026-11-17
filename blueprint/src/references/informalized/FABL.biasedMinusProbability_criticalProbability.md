<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedAnalysis.lean :: FABL.biasedMinusProbability_criticalProbability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Critical Probability Event

**Claim.** At the critical probability of a monotone, nonconstant Boolean function, the biased-minus probability of the function equals $1/2$.

**Proof.** The critical probability lies in $(0,1)$, so it also lies in $[0,1]$ and can be used as the parameter of the biased-minus probability. The polynomial-to-event-measure identity (\texttt{FABL.biasedMinusProbabilityPolynomial_eq}) rewrites that probability as the biased-minus probability polynomial evaluated at the same parameter. The critical-level identity (\texttt{FABL.biasedMinusProbabilityPolynomial_criticalProbability}) says this polynomial value is $1/2$, proving the claim.

**Key facts.** `FABL.criticalProbability_mem_Ioo`, `FABL.biasedMinusProbabilityPolynomial_eq`, `FABL.biasedMinusProbabilityPolynomial_criticalProbability`.
