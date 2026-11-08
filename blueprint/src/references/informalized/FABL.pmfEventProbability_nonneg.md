<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/Reasonableness.lean :: FABL.pmfEventProbability_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegative Event Probability

**Claim.** For a probability mass function on a finite set, the probability assigned to any event is nonnegative.

**Proof.** By definition, event probability is the expectation of the indicator of the event. At each point this indicator is either $0$ or $1$, hence is nonnegative. The nonnegativity of expectation for a pointwise nonnegative function (\texttt{pmfExpectation\_nonneg}) gives the result.

**Key facts.** `FABL.pmfExpectation_nonneg`.
