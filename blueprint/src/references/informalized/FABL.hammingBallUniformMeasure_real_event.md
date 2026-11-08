<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/HammingBallLimit.lean :: FABL.hammingBallUniformMeasure_real_event -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform probability of an event

**Claim.** For every $n\ge 0$ and every predicate $P$ on the sign cube, the measure of the event $\{x:P(x)\}$ under the uniform distribution equals the uniform probability of $P$.

**Proof.** Because the sign cube is finite, the indicator of $\{x:P(x)\}$ is measurable, and its integral is the measure of that event. The integral against the measure associated to the uniform distribution equals the uniform expectation (\texttt{integral\_uniformPMF\_eq\_expect}). Thus the event measure is the expectation of the indicator of $P$. At each point this indicator is $1$ when $P$ holds and $0$ otherwise, which is exactly the defining integrand for the uniform probability. Hence the two quantities agree.

**Key facts.** `FABL.integral_uniformPMF_eq_expect`.
