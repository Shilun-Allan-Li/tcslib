<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/LowDegree.lean :: FABL.lowDegreeFourierEstimatorProgram_of_totalInfluence_failure_le_one_tenth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Total Influence Learning Bound

**Claim.** If the target’s total influence is at most $t$, then the low-degree Fourier estimator at the degree determined by $t$ and $\epsilon$ has probability at most $1/10$ of producing a hypothesis with relative Hamming error greater than $\epsilon$.

**Proof.** The total-influence concentration result gives Fourier concentration through the degree $\lceil 2t/\epsilon\rceil$, with tail mass at most $\epsilon/2$ ($\texttt{isFourierSpectrumConcentratedUpTo\_totalInfluenceLearningDegree}$). The low-degree estimator failure bound applied at this degree then bounds the probability of relative error exceeding $\epsilon$ by $1/10$.

**Key facts.** `FABL.isFourierSpectrumConcentratedUpTo_totalInfluenceLearningDegree`, `FABL.lowDegreeFourierEstimatorProgram_failureProbability_le_one_tenth`.
