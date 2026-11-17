<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/MatrixProductVerification.lean :: FABL.matrixProductSmallBiasRandomBits_isBigO -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Asymptotic random-bit bound

**Claim.** As $n\to\infty$, the number of random bits specified for dimension $n$ is $O(\lceil\log_2(n+1)\rceil+1)$.

**Proof.** The pointwise estimate that the random-bit count is at most four times the logarithmic scale gives a uniform constant bound on the ratio of the corresponding real-valued functions: the natural-number quantities are viewed as real numbers, whose norms are themselves. A function bounded in this way is big-O of the logarithmic scale, by the bounded-witness criterion for big-O.

**Key facts.** `FABL.matrixProductSmallBiasRandomBits_le`.
