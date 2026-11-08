<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductLpInequalities.lean :: FABL.coordinateConditionalAbsMoment_eq_coordinateProjection -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Conditional Absolute Moment as Projection

**Claim.** For a finite sample space with law $\pi$, the conditional $p$th absolute moment about the mean after resampling coordinate $i$ equals the coordinate projection of the $p$th power of the absolute coordinate Laplacian.

**Proof.** Fix the other coordinates at $x$. By the coordinate-projection formula (\texttt{coordinateProjection\_apply}), projecting a function at $x$ is precisely averaging its values over replacements of coordinate $i$. In particular, the average of $f$ under this resampling is the value of its coordinate projection at $x$. At a replacement input $x'$ obtained by changing coordinate $i$, the same projection has the same value as at $x$ (\texttt{coordinateProjection\_replaceCoordinate}), since the projection averages over that coordinate and depends only on the other coordinates. Therefore the coordinate Laplacian at each such $x'$ is the resampled value of $f$ minus the resampling mean. Averaging the absolute $p$th power of this difference gives exactly the defining conditional absolute moment.

**Key facts.** `FABL.coordinateProjection_apply`, `FABL.coordinateProjection_replaceCoordinate`.
