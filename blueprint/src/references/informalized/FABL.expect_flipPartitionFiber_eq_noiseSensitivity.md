<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/UniformNoiseStability.lean :: FABL.expect_flipPartitionFiber_eq_noiseSensitivity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Partition Flips Give Noise Sensitivity

**Claim.** Averaging over a uniformly chosen coordinate labeling and a uniform sign vector, the probability that flipping the coordinates labeled $j$ changes $f$ equals the noise sensitivity of $f$ at rate $1/m$.

**Proof.** Set $\delta=1/m$. Since $m>0$, this lies in $[0,1]$ (`inverseDimension_mem_Icc`), and therefore $\rho=1-2\delta$ lies in $[-1,1]$ (`one_sub_two_mul_mem_Icc`). Fix a starting point $x$. Under a uniform labeling, each coordinate is labeled $j$ with probability $1/m$; the induced sign vector after flipping those coordinates has the same distribution as the noise kernel at correlation $\rho$. This distributional identity is the uniform-partition-to-noise-kernel result (`map_uniformPartition_eq_noiseKernel`). Consequently, the average over labelings of the indicator that the flip changes $f(x)$ equals the noise-kernel expectation of the corresponding indicator. Average this identity over uniform $x$. Interchanging the two finite averages and expressing the uniform averages as expectations under uniform PMFs (`pmfExpectation_uniformPMF_eq_expect`) gives the average first over $x$ and then over the noise kernel. The expectation of this two-stage experiment is the expectation under the bind of the uniform starting-point PMF with the noise kernel (`pmfExpectation_bind`). The map-expectation rule (`pmfExpectation_map`) identifies the indicator on the resulting pair with the indicator that the two function values differ. By the definition of noise sensitivity, this is exactly the claimed quantity.

**Key facts.** `FABL.inverseDimension_mem_Icc`, `FABL.one_sub_two_mul_mem_Icc`, `FABL.map_uniformPartition_eq_noiseKernel`, `FABL.pmfExpectation_uniformPMF_eq_expect`, `FABL.pmfExpectation_bind`, `FABL.pmfExpectation_map`.
