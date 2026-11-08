<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/SmallBias.lean :: FABL.ProbabilityDensity.isBiased_iff_isFourierRegular -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equivalence of two bias conditions

**Claim.** A probability density is $\varepsilon$-biased exactly when its corresponding function on the sign cube is $\varepsilon$-Fourier-regular.

**Proof.** First suppose the density is $\varepsilon$-biased, and take a nonempty set of coordinates $S$. Choose the vector $\gamma$ whose nonzero coordinates are exactly those in $S$, using the identification between vectors in $\mathbb F_2^n$ and subsets of coordinates. Its support is $S$. Since $S$ is nonempty, $\gamma\ne0$. The Fourier coefficient of the associated sign-cube function at $S$ equals the vector Fourier coefficient of the density at $\gamma$ (`vectorFourierCoeff_eq_fourierCoeff_binaryFunctionOnSignCube`), so its absolute value is at most $\varepsilon$ by the bias hypothesis. This proves Fourier regularity.

Conversely, suppose the associated function is $\varepsilon$-Fourier-regular, and take any nonzero vector $\gamma$. Its support is nonempty: if it were empty, every coordinate of $\gamma$ would be zero, contradicting $\gamma\ne0$. Apply Fourier regularity to this support. The same identity between the two Fourier coefficients shows that the absolute value of the vector Fourier coefficient at $\gamma$ is at most $\varepsilon$. Hence the density is $\varepsilon$-biased.

**Key facts.** `FABL.mem_f₂Support`, `FABL.vectorFourierCoeff_eq_fourierCoeff_binaryFunctionOnSignCube`.
