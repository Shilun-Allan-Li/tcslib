<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Minimax/ConvexMinimaxNoRegret.lean :: OnlineLearning.theorem71_compactApproximation_of_jointContinuous_compact -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Compact Approximation from Joint Continuity

**Claim.** Under the convex-compact minimax hypotheses, compactness of $Y$ and joint continuity on $X\times Y$ imply that every positive tolerance admits a nonempty finite row sample whose lower value is at most the full lower value plus that tolerance.

**Proof.** Joint continuity on the compact product gives uniform equicontinuity in the row variable (`theorem71_uniformEquicontinuity_of_jointContinuous_compact`). Apply the compact-approximation result for uniformly equicontinuous payoffs (`theorem71_compactApproximation_of_uniformEquicontinuity`) with the given minimax hypotheses. It supplies the required nonempty finite sample and value bound.

**Key facts.** `OnlineLearning.theorem71_uniformEquicontinuity_of_jointContinuous_compact`, `OnlineLearning.theorem71_compactApproximation_of_uniformEquicontinuity`.
