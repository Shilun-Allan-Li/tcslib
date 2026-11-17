<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Minimax/ConvexMinimaxNoRegret.lean :: OnlineLearning.convex_compact_minimax_noRegret_jointCompact_normalized -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Normalized Convex-Concave Minimax Equality

**Claim.** Under the stated minimax hypotheses, compactness of $Y$, joint continuity, and the normalization $0\le f\le1$ on $X\times Y$, the minimax equality holds.

**Proof.** The proof combines two ingredients through the theorem-71 route. The normalized finite no-regret bound supplies the finite-game estimate required by that route. Joint continuity on the compact product, together with compactness of $Y$, supplies its compact-approximation condition. Applying the route theorem to these two ingredients gives the minimax equality.

**Key facts.** `OnlineLearning.convex_compact_minimax_of_theorem71_route`, `OnlineLearning.theorem71_finiteNoRegretBound_normalized`, `OnlineLearning.theorem71_compactApproximation_of_jointContinuous_compact`.
