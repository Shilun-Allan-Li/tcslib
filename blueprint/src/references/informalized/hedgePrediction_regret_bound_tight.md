<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Hedge/ConvexPrediction.lean :: hedgePrediction_regret_bound_tight -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tight Regret Bound for Convex Predictions

**Claim.** Under the stated convexity and validity assumptions, Hedge’s cumulative prediction loss exceeds the best expert’s cumulative loss by at most $\frac{\ln N}{\eta}+\frac{\eta T}{8}$.

**Proof.** Apply the cumulative Jensen bound (`hedgePredictionCumLoss_le_hedgeCumLoss`) to compare the prediction losses with the cumulative Hedge loss on the induced loss sequence. The tight Hedge regret theorem for valid loss sequences (`hedge_regret_bound_tight`) bounds that cumulative Hedge loss minus the best expert’s cumulative loss by $\frac{\ln N}{\eta}+\frac{\eta T}{8}$. Combining the two inequalities gives the stated bound.

**Key facts.** `hedgePredictionCumLoss_le_hedgeCumLoss`, `hedge_regret_bound_tight`.
