<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/Tensorization.lean :: BooleanAnalysis.Hypercontractivity.FiniteTensorization.pair_tensorization -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tensorization of Pairing Estimates

**Claim.** Coordinatewise weighted pairing bounds tensorize: the pairing on the product space is bounded by the product-space weighted $p$-norm of the first function times the weighted $r$-norm of the second.

**Proof.** Proceed by induction on the number of coordinates. With no coordinates, the claim reduces to $f g\le |f||g|$, which follows from $fg\le|fg|$. For the induction step, separate the first coordinate from the remaining coordinates and write each product-space sum as an outer sum over the remaining coordinates and an inner sum over the first coordinate. For a fixed pair of remaining-coordinate points, apply the assumed one-coordinate pairing bound to the two slices of $f$ and $g$. This replaces their first-coordinate pairing by the product of the first-coordinate weighted $p$- and $r$-norms; call these slice norms $F$ and $G$. The remaining kernel product is nonnegative, so this replacement preserves the inequality after summing. Apply the induction hypothesis to $F$ and $G$ on the remaining coordinates. Finally, the moment identity in the proof shows that the product-space weighted moments of these slice norms equal the original weighted moments of $f$ and $g$, respectively. This yields the desired bound.
