<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/FiniteFamily.lean :: FABL.finiteFamilyFourierEstimatorOutput_support -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Estimator hypothesis support

**Claim.** The support of the resulting Fourier estimator hypothesis is exactly $\mathcal{F}$.

**Proof.** The estimator output is defined by `ofCoefficients`, which forms the hypothesis with support $\mathcal{F}$ and assigns its coefficients from the sample data. Thus its support is $\mathcal{F}$.
