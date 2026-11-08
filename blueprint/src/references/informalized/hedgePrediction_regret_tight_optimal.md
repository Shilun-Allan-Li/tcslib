<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Hedge/ConvexPrediction.lean :: hedgePrediction_regret_tight_optimal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Optimal-Rate Regret Bound for Convex Predictions

**Claim.** With the learning rate $\sqrt{8\ln N/T}$, the cumulative loss of Hedge’s convex weighted-average predictions minus the best expert’s cumulative loss is at most $\sqrt{(T/2)\ln N}$.

**Proof.** Use the cumulative Jensen bound (`hedgePredictionCumLoss_le_hedgeCumLoss`) at the specified learning rate to bound prediction loss by cumulative Hedge loss on the induced loss sequence. The optimal-rate Hedge regret theorem (`hedge_regret_tight_optimal`), applicable because $T>0$, $N>1$, and the induced losses are valid, bounds the latter regret by $\sqrt{(T/2)\ln N}$. Combining these inequalities proves the claim.

**Key facts.** `hedgePredictionCumLoss_le_hedgeCumLoss`, `hedge_regret_tight_optimal`.
