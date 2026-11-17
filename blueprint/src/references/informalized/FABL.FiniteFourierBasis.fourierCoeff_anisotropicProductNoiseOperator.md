<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.FiniteFourierBasis.fourierCoeff_anisotropicProductNoiseOperator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier coefficients under product noise

**Claim.** Under the anisotropic product noise transform, the Fourier coefficient at $a$ is multiplied by the product of coordinate weights, where coordinate $i$ has weight $1$ when $a(i)$ is the constant index and $\rho_i$ otherwise.

**Proof.** Define $c(b)$ to be the product of the coordinate weights associated with $b$, multiplied by the Fourier coefficient of $f$ at $b$. By the definition of the anisotropic noise transform, its value at every input is the finite Fourier expansion with coefficients $c(b)$. Uniqueness of Fourier expansions (\texttt{fourier_expansion_unique}) identifies this coefficient function with the transform's Fourier coefficient function. Evaluating that equality at $a$ gives the asserted formula.

**Key facts.** `FABL.FiniteFourierBasis.fourier_expansion_unique`.
