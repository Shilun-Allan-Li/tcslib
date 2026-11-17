<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LowDegreeSpectralConcentration.lean :: FABL.fourierDegree_firstCoordinateSlice_one_le_pred_of_neg_one_eq_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree of a slice when the opposite vanishes

**Claim.** If the function has Fourier degree at most $k$, with $k>0$, and its restriction at first coordinate $-1$ is zero, then its restriction at first coordinate $1$ has Fourier degree at most $k-1$.

**Proof.** Take any frequency set $S$ with $|S|>k-1$, hence $|S|\ge k$. Its tail frequency with the first coordinate adjoined has size $|S|+1>k$: the first coordinate is absent from the tail (`zero_notMem_tailFrequency`), and the tail has the same cardinality as $S$ (`card_tailFrequency`). The original function's Fourier coefficient at this enlarged set is therefore zero by the degree criterion (`fourierDegree_le_iff`). The enlarged-frequency coefficient identity (`fourierCoeff_insert_zero_tailFrequency`) says this is half the difference between the coefficients of the two slices at $S$. The coefficient for the slice at $-1$ vanishes because that slice is identically zero, so the coefficient for the slice at $1$ vanishes as well. The degree criterion now gives degree at most $k-1$.

**Key facts.** `FABL.fourierDegree_le_iff`, `FABL.zero_notMem_tailFrequency`, `FABL.card_tailFrequency`, `FABL.fourierCoeff_insert_zero_tailFrequency`.
