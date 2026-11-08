<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevin/RestrictedWeights.lean :: FABL.fourierOneNorm_eq_spectralPNorm_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier norm and spectral one norm

**Claim.** The Fourier one norm of a sign-cube function equals the spectral $1$-norm of the corresponding function on $(\mathbb F_2)^n$.

**Proof.** The spectral $1$-norm is the sum of the absolute values of the vector Fourier coefficients (`spectralPNorm_one_eq_sum_abs`). Reindex this sum by the bijection from binary-cube vectors to coordinate subsets. The coefficient correspondence identifies each vector Fourier coefficient with the sign-cube Fourier coefficient of the transported function (`vectorFourierCoeff_eq_fourierCoeff_binaryFunctionOnSignCube`). For the function obtained by composing $f$ with the bit-to-sign map, transporting it back to the sign cube recovers $f$ pointwise. The reindexed sum is therefore exactly the Fourier one norm of $f$.

**Key facts.** `FABL.spectralPNorm_one_eq_sum_abs`, `FABL.vectorFourierCoeff_eq_fourierCoeff_binaryFunctionOnSignCube`.
