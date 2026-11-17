<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdComplements.lean :: FABL.pmfExpectation_biasedSignPMF_negIndicator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Negative-Sign Probability

**Claim.** For $0<p<1$, the expected indicator of the event that a sign drawn from the biased distribution equals $-1$ is $p$.

**Proof.** Apply the expectation formula for the biased sign distribution (\texttt{FABL.pmfExpectation\_biasedSignPMF}) to the indicator that the sign is $-1$. Its value at $1$ is zero and its value at $-1$ is one, so the weighted sum $(1-p)\cdot 0+p\cdot 1$ equals $p$.

**Key facts.** `FABL.pmfExpectation_biasedSignPMF`.
