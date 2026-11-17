<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLCounterexample.lean :: FABL.pmfEventProbability_mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of Event Probability

**Claim.** If one event is contained in another on a finite probability space, then its probability is at most the probability of the larger event.

**Proof.** At every point, membership in the smaller event implies membership in the larger one. Thus the indicator of the smaller event is pointwise bounded by the indicator of the larger event. Monotonicity of expectation (\texttt{pmfExpectation_mono}) gives the corresponding inequality between their probabilities.

**Key facts.** `FABL.pmfExpectation_mono`.
