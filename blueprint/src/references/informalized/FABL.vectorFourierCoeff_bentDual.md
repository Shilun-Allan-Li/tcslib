<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/BentDual.lean :: FABL.vectorFourierCoeff_bentDual -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Coefficient of the Bent Dual

**Claim.** If $n$ is even, then for every $x\in\mathbb F_2^n$, the vector Fourier coefficient of the bent dual of $f$ at $x$ is $2^{-n/2}f(x)$.

**Proof.** By definition, the bent dual is the function whose value at each point is $2^{n/2}$ times the corresponding vector Fourier coefficient of $f$. Scaling a function scales each of its Fourier coefficients by the same constant (`FABL.vectorFourierCoeff_const_mul`). Applying Fourier inversion to the resulting function of Fourier coefficients (`FABL.vectorFourierCoeff_vectorFourierCoeff`) therefore gives $2^{n/2}2^{-n}f(x)$. Since $n$ is even, write $n=2k$, so $n/2=k$ and $2^{n/2}2^{-n}=2^k2^{-2k}=2^{-k}$. This is the asserted value.

**Key facts.** `FABL.vectorFourierCoeff_const_mul`, `FABL.vectorFourierCoeff_vectorFourierCoeff`.
