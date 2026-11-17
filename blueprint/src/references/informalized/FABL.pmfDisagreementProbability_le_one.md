<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductLTFNoiseCorrection.lean :: FABL.pmfDisagreementProbability_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Disagreement Probability Bound

**Claim.** For any finite sample space with a probability mass function, the probability that two functions disagree is at most $1$.

**Proof.** At each sample point, the disagreement indicator is either $0$ or $1$, so it is bounded by the constant function $1$. Monotonicity of expectation (\texttt{pmfExpectation_mono}) therefore bounds its expectation by the expectation of the constant function, which is $1$ (\texttt{pmfExpectation_const}).

**Key facts.** `FABL.pmfExpectation_mono`, `FABL.pmfExpectation_const`.
