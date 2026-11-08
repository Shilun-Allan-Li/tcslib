<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeF₂PolynomialLearning.lean :: FABL.measure_uniformPMF_event_eq_uniformProbability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform Event Probability as an Average

**Claim.** For a finite nonempty measurable space with measurable singletons, the uniform measure of an event equals the uniform average of its membership indicator.

**Proof.** Write the event's indicator as the function equal to $1$ on the event and $0$ outside it. Integrating this indicator gives the measure of the event, by the indicator integral formula. The integral under the uniform probability measure equals the uniform expectation (\texttt{integral\_uniformPMF\_eq\_expect}). That expectation is precisely the uniform average of the membership indicator, which is the defined uniform probability.

**Key facts.** `FABL.integral_uniformPMF_eq_expect`.
