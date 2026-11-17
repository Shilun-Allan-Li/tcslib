<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/BentFunctions.lean :: FABL.IsBent.spectralInfinityNorm_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bentness Determines the Spectral Infinity Norm

**Claim.** If $f$ is bent, then its spectral infinity norm is $\bigl(2^{\lfloor n/2\rfloor}\bigr)^{-1}$.

**Proof.** The spectral infinity norm is the supremum of the absolute values of all Walsh Fourier coefficients. Bentness states that every one of these absolute values equals $\bigl(2^{\lfloor n/2\rfloor}\bigr)^{-1}$. The supremum of this nonempty finite family of equal values is that same value.
