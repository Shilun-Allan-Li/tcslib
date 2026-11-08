<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/ExtremalBounds.lean :: FABL.degree_index_pos_of_zero_slice_nonzero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive degree from differing slices

**Claim.** If the slice of $f$ at coordinate value $1$ is zero, its slice at value $0$ is nonzero, and the algebraic degree of $f$ is at most $k$, then $k>0$.

**Proof.** Choose a set $S$ whose algebraic-normal-form coefficient in the zero slice is nonzero; such a coefficient exists for every nonzero function (`exists_anfCoeff_ne_zero_of_ne_zero`). The coefficient of that slice at $S$ equals the coefficient of $f$ at the tail-frequency set corresponding to $S$ (`anfCoeff_firstCoordinateSlice_zero`), so this latter coefficient is nonzero. The coefficient of the one slice at $S$ is zero because that slice is the zero function. The one-slice coefficient formula expresses it as the sum of the coefficient of $f$ at the tail-frequency set and its coefficient at the set obtained by adjoining coordinate $0$ (`anfCoeff_firstCoordinateSlice_one`). Since the first summand is nonzero and the sum is zero, the coefficient at the enlarged set is nonzero as well. The degree bound then bounds the size of this enlarged set by $k$ (`algebraicDegree_le_iff`). Coordinate $0$ is not in the tail-frequency set, and that set has the same size as $S$ (`zero_notMem_tailFrequency`, `card_tailFrequency`), so the enlarged set has size $|S|+1$. In particular, $k\ge1$.

**Key facts.** `FABL.exists_anfCoeff_ne_zero_of_ne_zero`, `FABL.anfCoeff_firstCoordinateSlice_zero`, `FABL.anfCoeff_firstCoordinateSlice_one`, `FABL.algebraicDegree_le_iff`, `FABL.zero_notMem_tailFrequency`, `FABL.card_tailFrequency`.
