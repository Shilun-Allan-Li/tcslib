<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LowDegreeSpectralConcentration.lean :: FABL.fourierDegree_firstCoordinateSlice_neg_one_le_pred_of_one_eq_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree of a slice when the other vanishes

**Claim.** If the function has Fourier degree at most $k$, with $k>0$, and its restriction at first coordinate $1$ is zero, then its restriction at first coordinate $-1$ has Fourier degree at most $k-1$.

**Proof.** To apply the degree criterion to the restriction at $-1$, take any frequency set $S$ with $|S|>k-1$. Since cardinalities are integers, $|S|\ge k$, so adjoining the first coordinate to its tail frequency gives a set of size $|S|+1>k$. The original function's coefficient at this enlarged frequency vanishes by its degree bound (`fourierDegree_le_iff`); the size computation uses that a tail frequency omits the first coordinate (`zero_notMem_tailFrequency`) and preserves cardinality (`card_tailFrequency`). The coefficient identity for adjoining the first coordinate (`fourierCoeff_insert_zero_tailFrequency`) expresses this vanishing coefficient as half the difference of the two slice coefficients. The coefficient from the slice at $1$ is zero because that entire slice is zero. Thus the coefficient at $S$ for the slice at $-1$ must also be zero. The degree criterion yields the claimed bound.

**Key facts.** `FABL.fourierDegree_le_iff`, `FABL.zero_notMem_tailFrequency`, `FABL.card_tailFrequency`, `FABL.fourierCoeff_insert_zero_tailFrequency`.
