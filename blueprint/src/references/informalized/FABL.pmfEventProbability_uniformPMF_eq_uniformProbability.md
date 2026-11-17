<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/Reasonableness.lean :: FABL.pmfEventProbability_uniformPMF_eq_uniformProbability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform Event Probability

**Claim.** For a finite nonempty set, the event probability under the uniform probability mass function equals the uniform probability of the event.

**Proof.** Unfold both definitions. The identity identifying expectation under the uniform probability mass function with uniform expectation (\texttt{pmfExpectation\_uniformPMF\_eq\_expect}) reduces the claim to equality of two expectations. Their integrands agree pointwise: whether the event holds or fails, both expressions assign respectively $1$ or $0$. Thus their finite expectations are equal.

**Key facts.** `FABL.pmfExpectation_uniformPMF_eq_expect`.
