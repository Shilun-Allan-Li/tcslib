<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/VectorFourier.lean :: FABL.IsVectorFourierGranular.intCast_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Integer Scaling Preserves Fourier Granularity

**Claim.** If every Fourier coefficient of a function is an integer multiple of $\varepsilon$, then the same holds after multiplying the function by any integer.

**Proof.** Apply the coefficientwise characterization of vector Fourier granularity (`isVectorFourierGranular_iff`). At any frequency $\gamma$, write the original coefficient as $b\varepsilon$ for an integer $b$. Fourier coefficients scale linearly under multiplication by a constant (`vectorFourierCoeff_const_mul`), so the coefficient of the integer-scaled function is $a(b\varepsilon)=(ab)\varepsilon$. Because $ab$ is an integer, the scaled function has the stated granularity.

**Key facts.** `FABL.isVectorFourierGranular_iff`, `FABL.vectorFourierCoeff_const_mul`.
