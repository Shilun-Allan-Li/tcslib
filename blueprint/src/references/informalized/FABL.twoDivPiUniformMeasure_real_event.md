<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/TwoDivPi.lean :: FABL.twoDivPiUniformMeasure_real_event -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform measure of an event

**Claim.** For any decidable property $P$ of sign vectors, the measure of the event where $P$ holds equals the uniform probability of $P$.

**Proof.** Because the sign-vector space is finite, the event $\{x:P(x)\}$ is measurable. Its measure is the integral of its indicator function. Replacing integration under the measure induced by the uniform probability law with expectation under that law (`FABL.integral_uniformPMF_eq_expect`) turns this into the expectation of the indicator of $P$. Pointwise, that indicator is $1$ when $P(x)$ holds and $0$ otherwise, exactly the function used to define uniform probability. The two quantities therefore agree.

**Key facts.** `FABL.integral_uniformPMF_eq_expect`.
