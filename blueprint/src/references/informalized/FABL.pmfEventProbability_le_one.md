<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/Reasonableness.lean :: FABL.pmfEventProbability_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Event Probability Bound

**Claim.** The probability of any event on a finite probability space is at most $1$.

**Proof.** The indicator of an event is pointwise at most the constant function $1$. By monotonicity of expectation (\texttt{pmfExpectation_mono}), its expectation is at most the expectation of that constant function, which equals $1$ (\texttt{pmfExpectation_const_one}).

**Key facts.** `FABL.pmfExpectation_const_one`, `FABL.pmfExpectation_mono`.
