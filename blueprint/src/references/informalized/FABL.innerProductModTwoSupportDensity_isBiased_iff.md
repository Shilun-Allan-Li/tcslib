<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/InnerProductSupportDensity.lean :: FABL.innerProductModTwoSupportDensity_isBiased_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Bias Criterion for the Support Density

**Claim.** For positive $m$ and real $\varepsilon$, the support density is $\varepsilon$-biased exactly when $\varepsilon\ge (2^{-m})/(1-2^{-m})$.

**Proof.** For the forward implication, choose a nonzero frequency supported at one coordinate of the first block. It is nonzero because its value at that coordinate is $1$. The absolute Fourier coefficient at this frequency is exactly $(2^{-m})/(1-2^{-m})$, by the formula for every nonzero frequency (\texttt{abs_vectorFourierCoeff_innerProductModTwoSupportDensity}). The definition of being $\varepsilon$-biased bounds this coefficient by $\varepsilon$, yielding the claimed inequality. Conversely, that same coefficient formula gives the absolute coefficient at every nonzero frequency as $(2^{-m})/(1-2^{-m})$. If this quantity is at most $\varepsilon$, every required Fourier bound holds, so the density is $\varepsilon$-biased.

**Key facts.** `FABL.abs_vectorFourierCoeff_innerProductModTwoSupportDensity`.
