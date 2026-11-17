<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/BentFunctions.lean :: FABL.isBent_of_spectralInfinityNorm_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bentness from the spectral maximum

**Claim.** If $n$ is even and $f$ is sign-valued on the binary cube, then a spectral infinity norm of $(2^{n/2})^{-1}$ implies that every Fourier coefficient has absolute value $(2^{n/2})^{-1}$, so $f$ is bent.

**Proof.** Write $n=2k$, so $n/2=k$. By the definition of spectral infinity norm as the maximum absolute Fourier coefficient, every coefficient has absolute value at most $2^{-k}$. Suppose one coefficient were strictly smaller. Squaring, that coefficient's square would be strictly less than $2^{-2k}$, while all other squared coefficients are at most $2^{-2k}$. Summing over all $2^{2k}$ frequencies would then give a total strictly less than one. But Parseval's identity for a sign-valued function says that the sum of squared Fourier coefficients is one (`sum_sq_vectorFourierCoeff_eq_one`). This contradiction rules out a strictly smaller coefficient. Thus every absolute coefficient equals $2^{-k}$, as required for bentness.

**Key facts.** `FABL.sum_sq_vectorFourierCoeff_eq_one`.
