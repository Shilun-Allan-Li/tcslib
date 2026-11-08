<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/InputMoments.lean :: BooleanAnalysis.GaussianSpace.hasInvarianceMoments_pi_coordinate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Invariance moments of a product coordinate

**Claim.** For a finite product of probability spaces, if each coordinate function satisfies the invariance moment conditions, then the function on the product obtained by applying one chosen coordinate function to that coordinate also satisfies those conditions under the product measure.

**Proof.** Fix a coordinate $i$. Under the product measure, the coordinate projection $x\mapsto x_i$ has the same distribution as the identity map on the $i$th factor: both maps are measurable, and the product-measure evaluation identity shows their pushforward measures agree. Composing these maps with the measurable function $X_i$ preserves equality in distribution. The invariance-moment properties transfer under equality in distribution (\texttt{HasInvarianceMoments.identDistrib}), so the selected coordinate function on the product has the required conditions.

**Key facts.** `BooleanAnalysis.GaussianSpace.HasInvarianceMoments.identDistrib`.
