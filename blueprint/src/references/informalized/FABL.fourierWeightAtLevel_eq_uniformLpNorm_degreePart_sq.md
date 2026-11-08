<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter01/BasicFourierFormulas.lean :: FABL.fourierWeightAtLevel_eq_uniformLpNorm_degreePart_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Level weight and degree-part norm

**Claim.** For every $k$ and $f$, the Fourier weight at level $k$ equals the square of the uniform $L^2$ norm of the degree-$k$ part of $f$.

**Proof.** The square of the uniform $L^2$ norm is the uniform inner product of the degree-$k$ part with itself, by the identity relating the squared norm to that inner product. Parseval expresses this inner product as the sum of the squares of the Fourier coefficients of the degree-$k$ part. The coefficient of that part at a set $T$ is the original coefficient when $|T|=k$ and zero otherwise (the degree-part coefficient formula, `fourierCoeff_degreePart`). Squaring these coefficients leaves precisely the sum over sets of size $k$, which is the level-$k$ Fourier weight.

**Key facts.** `FABL.uniformLpNorm_two_sq_eq_uniformInner`, `FABL.parseval`, `FABL.fourierCoeff_degreePart`.
