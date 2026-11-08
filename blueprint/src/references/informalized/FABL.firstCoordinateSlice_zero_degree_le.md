<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/ExtremalBounds.lean :: FABL.firstCoordinateSlice_zero_degree_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree bound for the zero slice

**Claim.** If a Boolean function on $n+1$ coordinates has algebraic degree at most $k$, then its restriction to the slice where the first coordinate is zero has algebraic degree at most $k$.

**Proof.** Use the characterization of an algebraic-degree bound by support coefficients: every monomial with nonzero coefficient has size at most $k$ (`algebraicDegree_le_iff`). For any monomial index $S$ on the remaining coordinates, the coefficient of the sliced function equals the coefficient of the original function at the corresponding tail frequency (`anfCoeff_firstCoordinateSlice_zero`). Thus, whenever the sliced coefficient is nonzero, the original coefficient at that tail frequency is nonzero. Its cardinality is the cardinality of $S$, so the original degree bound gives $|S|\le k$. Applying the same characterization to the sliced function proves the result.

**Key facts.** `FABL.algebraicDegree_le_iff`, `FABL.anfCoeff_firstCoordinateSlice_zero`.
