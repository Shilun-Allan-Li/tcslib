<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/OrthogonalDecomposition.lean :: FABL.FiniteFourierBasis.productMean_restrict_orthogonalComponent_eq_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Vanishing Mean After Coordinate Restriction

**Claim.** If $S$ contains at least two coordinates and $i\in S$, then fixing coordinate $i$ in the orthogonal component of $f$ supported on $S$ gives a function with product mean zero.

**Proof.** Let $g$ be the orthogonal component supported on $S$ after coordinate $i$ has been fixed. The restriction identity (`restrictProductCoordinate_orthogonalComponent_eq`) says that this restricted function is itself the orthogonal component of $g$ supported on $S\setminus\{i\}$. Since $i\in S$ and $|S|\ge 2$, this remaining set is nonempty. Now take the Fourier coefficient at the all-constant multi-index, which equals the product mean (`fourierCoeff_zeroMultiIndex`). The coefficient formula for an orthogonal component (`fourierCoeff_orthogonalComponent`) makes this coefficient zero: the all-constant multi-index has empty support, which cannot equal the nonempty set $S\setminus\{i\}$. Hence the product mean of the restricted component is zero.

**Key facts.** `FABL.FiniteFourierBasis.restrictProductCoordinate_orthogonalComponent_eq`, `FABL.FiniteFourierBasis.fourierCoeff_zeroMultiIndex`, `FABL.FiniteFourierBasis.fourierCoeff_orthogonalComponent`.
