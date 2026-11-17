<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/NoiseOperator.lean :: FABL.kernelNoiseOperator_eq_noiseOperator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Kernel and spectral noise operators

**Claim.** For $\rho\in[-1,1]$, averaging a real-valued function against the independent coordinate noise kernel agrees with the noise operator that multiplies each Walsh monomial of degree $|S|$ by $\rho^{|S|}$.

**Proof.** It is enough to compare the two linear operators on the Walsh basis and then evaluate at each cube point. The parity orthonormal basis result identifies the basis vector indexed by $S$ with the Walsh monomial (`parity_orthonormal_basis`). On this monomial, the spectral operator acts by multiplication by $\rho^{|S|}$ (`noiseOperator_monomial_apply`). The kernel operator gives the same value: the expected monomial after independent coordinate noise is $\rho^{|S|}$ times its original value (`pmfExpectation_noiseKernel_monomial`). Since the operators agree on every basis vector, they agree on all functions.

**Key facts.** `FABL.parity_orthonormal_basis`, `FABL.noiseOperator_monomial_apply`, `FABL.pmfExpectation_noiseKernel_monomial`.
