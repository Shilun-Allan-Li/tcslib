<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/NoiseOperator.lean :: FABL.correlatedAgreementProbability_eq_one_sub_disagreement -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement and Disagreement Probabilities

**Claim.** For the correlated pair distribution, the probability that the Boolean function agrees on the two inputs is one minus the probability that it disagrees.

**Proof.** Write $p$ for the probability mass function of the correlated pair. For every pair $(x,y)$, exactly one of $f(x)=f(y)$ and $f(x)\ne f(y)$ holds. Hence the indicator of agreement equals one minus the indicator of disagreement. Taking expectation under $p$, linearity of expectation (`pmfExpectation_sub`) gives the expectation of the constant one minus the disagreement probability. The expectation of the constant one is $1$ (`pmfExpectation_const_one`), proving the identity.

**Key facts.** `FABL.pmfExpectation_sub`, `FABL.pmfExpectation_const_one`.
