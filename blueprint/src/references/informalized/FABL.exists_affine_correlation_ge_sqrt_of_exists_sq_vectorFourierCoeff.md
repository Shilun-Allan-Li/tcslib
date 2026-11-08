<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DerandomizedBLR.lean :: FABL.exists_affine_correlation_ge_sqrt_of_exists_sq_vectorFourierCoeff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Affine Approximation from a Large Fourier Coefficient

**Claim.** If some vector Fourier coefficient of the real sign encoding of $f$ has square at least $t$, then an affine function has sign correlation at least $\sqrt t$ with it and relative Hamming distance at most $1/2-\sqrt t/2$.

**Proof.** Choose a frequency $\gamma$ with coefficient square at least $t$. Since the absolute value of a real number is nonnegative, the square-root comparison gives $\sqrt t\le|\widehat F(\gamma)|$, where $F$ is the real sign encoding. Choose the constant term $b$ so its sign agrees with the coefficient: use the positive sign when the coefficient is nonnegative, and the negative sign otherwise. The sign encoding of the affine function is this constant sign times the Walsh character (`realSignEncodedFunction_affineFunction`, `affineSignFunction_apply`), so its correlation with $F$ equals $|\widehat F(\gamma)|$; the coefficient is the uniform expectation against that character (`vectorFourierCoeff_eq_expect`). This proves the correlation bound. The distance from $f$ to the affine function equals the distance between their sign encodings (`relativeHammingDist_realSignEncodedFunction`). The affine-sign distance formula `relativeHammingDist_affineSignFunction` expresses that distance as $1/2-|\widehat F(\gamma)|/2$. Using $|\widehat F(\gamma)|\ge\sqrt t$ gives the claimed upper bound.

**Key facts.** `FABL.isSignValued_realSignEncodedFunction`, `FABL.realSignEncodedFunction_affineFunction`, `FABL.affineSignFunction_apply`, `FABL.vectorFourierCoeff_eq_expect`, `FABL.relativeHammingDist_realSignEncodedFunction`, `FABL.relativeHammingDist_affineSignFunction`.
