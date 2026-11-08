<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/OrthogonalDecomposition.lean :: FABL.coordinateProjection_restrictProductCoordinate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinate projection and restriction

**Claim.** For distinct coordinates $i$ and $j$, projecting by averaging over all coordinates except $j$ commutes with fixing coordinate $i$ to a specified value.

**Proof.** Evaluate both sides at an arbitrary input $x$. The projection averages over resampled inputs, so it suffices to compare the inputs to $f$ in the two integrands. At coordinate $i$, both use the fixed value; at coordinate $j$, both use the resampled value; and at all other coordinates, both retain the corresponding value from $x$. Since $i\ne j$, these choices agree coordinate by coordinate. The integrands are equal for every resampled input, and hence their averages are equal.
