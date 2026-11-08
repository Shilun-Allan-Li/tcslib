<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/FourierEstimation.lean :: FABL.fourierObservation_hasSubgaussianMGF -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Subgaussian Fourier Observations

**Claim.** For a Boolean-valued target and any frequency set $S$, the Fourier observation centered at its expectation has a subgaussian moment generating function with parameter $1$ under the uniform input distribution.

**Proof.** The observation is a product of two signs, so it lies in $[-1,1]$ for every input. A random variable supported in this interval has a subgaussian moment generating function with parameter $1$ after centering, by the bounded-interval subgaussian estimate. The observation's expectation under the uniform distribution is its Fourier coefficient, so this centered variable is precisely the one in the claim.

**Key facts.** `FABL.fourierObservation_mem_Icc`, `FABL.integral_fourierObservation_uniformPMF`.
