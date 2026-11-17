<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/Program.lean :: FABL.two_mul_exp_neg_fourierEstimatorSampleCount_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Estimator Failure Bound

**Claim.** For learning parameters $\varepsilon,\delta\in(0,1/2]$, the failure bound bits and sample count defined in the statement satisfy $2\exp(-m\varepsilon^2/2)\leq\delta$, where $m$ is the Fourier estimator sample count.

**Proof.** The sample exponent is at least the number of failure bits, by `FABL.fourierEstimatorFailureBits_le_sampleExponent`. Also $\log 2\leq1$, so multiplying this inequality by the nonnegative number of failure bits shows that the sample exponent is at least the number of failure bits times $\log 2$. Since the exponential function is increasing, this bounds $\exp(-m\varepsilon^2/2)$ above by $\exp(-B\log 2)=2^{-B}$, where $B$ is the number of failure bits. The defining choice of $B$ ensures $2/2^B\leq\delta$, by `FABL.two_div_pow_fourierEstimatorFailureBits_le`. Combining these bounds proves the claim.

**Key facts.** `FABL.fourierEstimatorFailureBits_le_sampleExponent`, `FABL.two_div_pow_fourierEstimatorFailureBits_le`.

**Caveat.** The supplied informal statement is corrupted; this claim follows the self-contained formal statement.
