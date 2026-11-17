<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Reverse/Basic.lean :: BooleanAnalysis.Hypercontractivity.noiseOp_const_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Homogeneity of the Noise Operator

**Claim.** For every real scalar $c$, the noise operator satisfies $T_\rho(cf)=cT_\rho f$.

**Proof.** At each point, expand the noise operator as a sum over Fourier characters. The Fourier coefficient of $cf$ at each character is $c$ times the corresponding coefficient of $f$ (`fourierCoeff_const_mul`). Pull this common scalar through the finite sum; each summand is then exactly $c$ times the corresponding summand defining $T_\rho f$.

**Key facts.** `BooleanAnalysis.Hypercontractivity.fourierCoeff_const_mul`.
