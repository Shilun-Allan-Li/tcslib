<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeInequalities.lean :: FABL.productCoordinateLaplacian_fixProductCoordinate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Commutation with fixing another coordinate

**Claim.** When $i\ne j$, applying the product coordinate Laplacian in coordinate $i$ commutes with fixing coordinate $j$ to a value $\omega$.

**Proof.** Write the coordinate Laplacian as the function minus its coordinate projection. The coordinate projection in direction $i$ commutes with fixing the distinct coordinate $j$ (`coordinateProjection_fixProductCoordinate`). Substituting this identity into the two expressions leaves the same function difference on both sides, proving the commutation.

**Key facts.** `FABL.coordinateProjection_fixProductCoordinate`.
