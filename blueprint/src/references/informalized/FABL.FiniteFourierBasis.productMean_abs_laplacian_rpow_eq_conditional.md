<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductLpInequalities.lean :: FABL.FiniteFourierBasis.productMean_abs_laplacian_rpow_eq_conditional -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Laplacian moment as a conditional moment

**Claim.** The product mean of $|L_i f|^p$ equals the product mean of the conditional centered absolute $p$th moment over coordinate $i$.

**Proof.** The conditional centered moment at a point is the coordinate projection of the function $|L_i f|^p$; this pointwise identification is \texttt{coordinateConditionalAbsMoment_eq_coordinateProjection}. Therefore its product mean is the mean of that projection. The product mean is invariant under projection onto any chosen set of coordinates, in particular all coordinates except $i$ (\texttt{productMean_projectOnCoordinates}), so it equals the product mean of $|L_i f|^p$.

**Key facts.** `FABL.coordinateConditionalAbsMoment_eq_coordinateProjection`, `FABL.FiniteFourierBasis.productMean_projectOnCoordinates`.
