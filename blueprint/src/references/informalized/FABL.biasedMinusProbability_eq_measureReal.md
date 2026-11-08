<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.biasedMinusProbability_eq_measureReal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Probability as Event Measure

**Claim.** For $p\in[0,1]$ and a Boolean function on the $n$-dimensional sign cube, the biased-minus probability equals the measure of the event that the function takes value $-1$ under the corresponding product distribution.

**Proof.** The biased-minus probability is the expectation, under the product probability mass function, of the indicator that $f(x)=-1$. First identify this indicator pointwise with the indicator function of the event $\{x:f(x)=-1\}$. The expectation-to-integral identity for a probability mass function (\texttt{FABL.pmfExpectation_eq_integral}) then expresses the expectation as the integral of that event indicator. Since the cube is finite, this event is measurable, and integrating its indicator gives its measure. This is the asserted event measure.

**Key facts.** `FABL.pmfExpectation_eq_integral`.
