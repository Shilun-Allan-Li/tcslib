<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/ExtremalBounds.lean :: FABL.anfCoeff_firstCoordinateSlice_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coefficient of the zero-coordinate slice

**Claim.** The coefficient at $S$ of the slice with first coordinate $0$ equals the coefficient of $f$ at the corresponding tail set $S^+$.

**Proof.** In the coefficient sum over subsets of the tail set $S^+$, every subset corresponds uniquely to a subset $T$ of $S$ via the tail-coordinate embedding. This correspondence preserves subset inclusion and is injective, so it gives a bijection between the two indexing families. Under it, the indicator cube of the tail set of $T$ is exactly the cube with first coordinate $0$ and tail equal to the indicator cube of $T$ (`f₂CubeOfFinset_tailFrequency`). Thus the corresponding summands agree, and so do the sums.

**Key facts.** `FABL.f₂CubeOfFinset_tailFrequency`.
