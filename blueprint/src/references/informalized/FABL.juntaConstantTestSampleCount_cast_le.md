<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/JuntaLearningReduction.lean :: FABL.juntaConstantTestSampleCount_cast_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Constant Accuracy Sample Bound

**Claim.** For every natural number $k$ and failure parameter $\delta\in(0,1/2]$, the Fourier estimator sample count at accuracy $1/2^{k+2}$ is at most $64\cdot4^k$ times the number of failure bits associated with $\delta$.

**Proof.** Apply the general sample-count bound (\texttt{fourierEstimatorSampleCount\_cast\_le}) with accuracy equal to the constant-testing accuracy. This gives an upper bound of $4$ times the failure-bit count divided by the square of that accuracy. Substituting $1/2^{k+2}$ for the accuracy, and using $2^{k+2}=4\cdot2^k$, the coefficient becomes $4(2^{k+2})^2=64\cdot4^k$.

**Key facts.** `FABL.fourierEstimatorSampleCount_cast_le`.
