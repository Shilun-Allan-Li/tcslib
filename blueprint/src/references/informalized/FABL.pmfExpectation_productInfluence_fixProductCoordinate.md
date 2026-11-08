<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeInequalities.lean :: FABL.pmfExpectation_productInfluence_fixProductCoordinate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influence Averaging Under Coordinate Fixing

**Claim.** For distinct coordinates $i$ and $j$, averaging over the value fixed at coordinate $j$ leaves the influence in coordinate $i$ unchanged.

**Proof.** The coordinate Laplacian in coordinate $i$ commutes with fixing a different coordinate $j$ (the fact `productCoordinateLaplacian_fixProductCoordinate`). Thus the influence of the function with coordinate $j$ fixed is the product expectation of the square of the coordinate-$i$ Laplacian of the original function, with coordinate $j$ fixed to the sampled value. Rewriting the inner product as an expectation (`pmfInner_eq_expect`) and the square as a second power identifies this quantity as the product mean of that squared Laplacian after fixing coordinate $j$. The mean-under-coordinate-fixing identity (`pmfExpectation_productMean_fixProductCoordinate`) says its average over the fixed value equals its original product mean. That original mean is exactly the influence in coordinate $i$.

**Key facts.** `FABL.productCoordinateLaplacian_fixProductCoordinate`, `FABL.pmfInner_eq_expect`, `FABL.pmfExpectation_productMean_fixProductCoordinate`.
