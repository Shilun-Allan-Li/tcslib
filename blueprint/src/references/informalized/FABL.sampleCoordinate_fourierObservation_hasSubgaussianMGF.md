<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/FourierEstimation.lean :: FABL.sampleCoordinate_fourierObservation_hasSubgaussianMGF -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Subgaussian Bound for a Sampled Fourier Observation

**Claim.** Under the product law of independent uniform cube inputs, the Fourier observation at any fixed sample coordinate, centered by its Fourier coefficient, has a subgaussian moment-generating-function bound with parameter $1$.

**Proof.** Fix the sample coordinate and view the uncentered Fourier observation there as a random variable on the product sample space. The observation always lies in $[-1,1]$ ( `fourierObservation_mem_Icc`). A random variable bounded in an interval of length two has the stated subgaussian moment-generating-function bound with parameter $1$. Its mean under the product law is the Fourier coefficient: integrating over the product space reduces to integrating the observation at the chosen coordinate, and the uniform-input expectation equals that coefficient ( `integral_fourierObservation_uniformPMF`). Centering by this mean therefore gives the claimed bound.

**Key facts.** `FABL.fourierObservation_mem_Icc`, `FABL.integral_fourierObservation_uniformPMF`.
