<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadTests.lean :: FABL.pmfExpectation_signPMFOfMean -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mean of a Sign Distribution

**Claim.** For a sign chosen to equal $1$ with probability $(1+\mu)/2$ and $-1$ otherwise, its expected value is $\mu$.

**Proof.** By the coordinate-noise expectation formula (`pmfExpectation_coordinateNoisePMF_signValue`), the expectation for noise parameter $\mu$ applied to the sign $1$ is $\mu$ times the value of that sign. Since the value of $1$ is $1$, this is $\mu$.

**Key facts.** `FABL.pmfExpectation_coordinateNoisePMF_signValue`.
