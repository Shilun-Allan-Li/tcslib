<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LowDegreeSpectralConcentration.lean :: FABL.degreeBound_pos_of_firstCoordinateSlice_one_ne_zero_of_neg_one_eq_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Nonzero Slice Forces Positive Degree Bound

**Claim.** If the restriction at $1$ is nonzero, the restriction at $-1$ is zero, and the Fourier degree of the original function is at most $k$, then $k$ is positive.

**Proof.** Assume instead that $k=0$. The nonzero restriction at $1$ has a nonzero Fourier coefficient at some set $S` (`exists_fourierCoeff_ne_zero_of_ne_zero`), while the zero restriction at $-1$ has coefficient zero there. The first-coordinate coefficient formula (`fourierCoeff_insert_zero_tailFrequency`) therefore makes the original function’s coefficient at the set formed by adjoining the first coordinate to the tail version of $S$ nonzero. Since the first coordinate is absent from the tail set, this set has size $|S|+1>0$. The degree bound, expressed as vanishing of coefficients above degree $k$ (`fourierDegree_le_iff`), forces that coefficient to vanish when $k=0$, a contradiction. Hence $k>0$.

**Key facts.** `FABL.exists_fourierCoeff_ne_zero_of_ne_zero`, `FABL.fourierCoeff_insert_zero_tailFrequency`, `FABL.zero_notMem_tailFrequency`, `FABL.card_tailFrequency`, `FABL.fourierDegree_le_iff`.
