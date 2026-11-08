<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/FourierEstimation.lean :: FABL.measure_centeredFourierObservation_sum_ge_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-sided Fourier sum tail bound

**Claim.** For independent uniform cube samples, the probability that the sum of the centered Fourier observations for a fixed set exceeds $m\varepsilon$ is at most $\exp(-m\varepsilon^2/2)$.

**Proof.** For each sample coordinate, subtract the true Fourier coefficient from the Fourier observation. The resulting random variables are independent under the product sampling measure, and each has a sub-Gaussian moment generating function with parameter $1$ by the centered-observation bound (`FABL.sampleCoordinate_fourierObservation_hasSubgaussianMGF`). The sub-Gaussian upper-tail inequality for a sum of independent variables therefore bounds the probability that their sum is at least $m\varepsilon$ by $\exp(-(m\varepsilon)^2/(2m))$. Simplifying the exponent gives the stated bound.

**Key facts.** `FABL.sampleCoordinate_fourierObservation_hasSubgaussianMGF`.
