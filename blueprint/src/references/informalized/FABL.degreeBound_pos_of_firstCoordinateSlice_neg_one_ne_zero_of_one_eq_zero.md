<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LowDegreeSpectralConcentration.lean :: FABL.degreeBound_pos_of_firstCoordinateSlice_neg_one_ne_zero_of_one_eq_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Nonzero Slice Forces Positive Degree Bound

**Claim.** If the restriction at $-1$ is nonzero, the restriction at $1$ is zero, and the Fourier degree of the original function is at most $k$, then $k$ is positive.

**Proof.** Assume instead that $k=0$. Since the restriction at $-1$ is nonzero, it has a nonzero Fourier coefficient at some set $S$ (`exists_fourierCoeff_ne_zero_of_ne_zero`). The zero restriction at $1$ has coefficient zero at the same set. The formula for a coefficient indexed by the first coordinate together with the tail frequencies (`fourierCoeff_insert_zero_tailFrequency`) then gives a nonzero coefficient of the original function at the set formed by adjoining the first coordinate to the tail version of $S$. The first coordinate is not in that tail set, so this enlarged set has size $|S|+1>0$. But the degree bound, in its coefficient-vanishing form (`fourierDegree_le_iff`), says every coefficient indexed by a set of size greater than $k=0$ is zero. This contradiction proves $k>0$.

**Key facts.** `FABL.exists_fourierCoeff_ne_zero_of_ne_zero`, `FABL.fourierCoeff_insert_zero_tailFrequency`, `FABL.zero_notMem_tailFrequency`, `FABL.card_tailFrequency`, `FABL.fourierDegree_le_iff`.
