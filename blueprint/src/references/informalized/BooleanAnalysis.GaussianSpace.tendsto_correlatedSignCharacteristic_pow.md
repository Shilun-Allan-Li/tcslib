<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/BlockCharacteristic.lean :: BooleanAnalysis.GaussianSpace.tendsto_correlatedSignCharacteristic_pow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian limit of correlated sign characteristics

**Claim.** The indicated $m$th power of the correlated sign characteristic converges to $\exp\!\left(-\frac{a^2+b^2+2\rho ab}{2}\right)$.

**Proof.** The preceding asymptotic calculation shows that $m$ times the correlated sign characteristic minus $1$ tends to $-(a^2+b^2+2\rho ab)/2$ (`tendsto_nat_mul_correlatedSignCharacteristic_sub_one`). The standard limit theorem for powers of terms of the form $1+u_m/m$ then gives convergence of the $m$th powers to the exponential of that limit. Expanding the characteristic's definition identifies the resulting sequence with the one stated.

**Key facts.** `BooleanAnalysis.GaussianSpace.tendsto_nat_mul_correlatedSignCharacteristic_sub_one`.
