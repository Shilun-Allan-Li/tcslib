<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.coordinateConditionalVariance_eq_coordinateProjection_sq_laplacian -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Conditional Variance as Projected Squared Laplacian

**Claim.** The variance of $f$ under resampling coordinate $i$ with the other coordinates fixed equals the coordinate projection of the squared coordinate Laplacian.

**Proof.** Fix $x$ and let $m$ be the average of $f$ over replacements of coordinate $i$. By the coordinate-projection formula (\texttt{coordinateProjection\_apply}), this average is the coordinate projection of $f$ at $x$. When coordinate $i$ is replaced in $x$, that projected value remains unchanged (\texttt{coordinateProjection\_replaceCoordinate}). Thus at each replacement input, the coordinate Laplacian is the resampled value of $f$ minus $m$. Squaring and averaging over the replacements gives the conditional variance, while the same average is, by the projection formula, the coordinate projection of the squared Laplacian at $x$.

**Key facts.** `FABL.coordinateProjection_apply`, `FABL.coordinateProjection_replaceCoordinate`.
