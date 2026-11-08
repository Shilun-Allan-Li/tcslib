<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/LowDegree.lean :: FABL.lowDegreeFourierEstimatorProgram_failureProbability_le_one_tenth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Failure probability under Fourier concentration

**Claim.** If the target’s Fourier spectrum is concentrated up to degree $k$ with tail weight at most $\varepsilon/2$, then the low-degree estimator with degree parameter $k$ has failure probability at most $1/10$.

**Proof.** The finite-family estimator’s failure guarantee applies when the spectrum is concentrated on the estimator’s chosen family. The equivalence between concentration on the low-degree Fourier family and concentration up to degree $k$ converts the given hypothesis into exactly this condition. Applying the finite-family guarantee then bounds the probability that the output’s relative Hamming distance exceeds $\varepsilon$ by $1/10$.

**Key facts.** `FABL.finiteFamilyFourierEstimatorProgram_failureProbability_le_one_tenth`, `FABL.isFourierSpectrumConcentratedOn_lowDegreeFourierFamily_iff`.
