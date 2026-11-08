<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/LowDegree.lean :: FABL.lowDegreeFourierEstimatorProgram_of_noiseSensitivity_failure_le_one_tenth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Noise Sensitivity Learning Bound

**Claim.** If the target’s noise sensitivity at rate $\delta\in(0,1/2]$ is at most $\epsilon/6$, then the low-degree Fourier estimator at the noise-sensitivity learning degree has probability at most $1/10$ of producing a hypothesis with relative Hamming error greater than $\epsilon$.

**Proof.** The noise-sensitivity concentration result says that under the stated bound on noise sensitivity, the target’s Fourier spectrum is concentrated through degree $\lceil 1/\delta\rceil$, with tail mass at most $\epsilon/2$ ($\texttt{isFourierSpectrumConcentratedUpTo\_noiseSensitivityLearningDegree}$). Apply the low-degree estimator failure bound to this concentration statement at that degree. It yields the asserted probability of error greater than $\epsilon$ being at most $1/10$.

**Key facts.** `FABL.isFourierSpectrumConcentratedUpTo_noiseSensitivityLearningDegree`, `FABL.lowDegreeFourierEstimatorProgram_failureProbability_le_one_tenth`.
