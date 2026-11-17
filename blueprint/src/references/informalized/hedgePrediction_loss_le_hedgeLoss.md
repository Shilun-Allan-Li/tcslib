<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Hedge/ConvexPrediction.lean :: hedgePrediction_loss_le_hedgeLoss -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Round Jensen Bound

**Claim.** At each round, the loss of Hedge’s weighted-average prediction is at most the expected loss of the experts’ predictions under the Hedge distribution.

**Proof.** At the fixed round, the Hedge prediction is a finite weighted average of the experts’ predictions. Its weights are nonnegative (`hedgeDist_nonneg`) and sum to one (`hedgeDist_sum`), and each expert prediction belongs to the convex set $S$. Jensen’s inequality for a convex function on a convex set therefore bounds the loss at this weighted average by the same weighted average of the experts’ losses. Expanding the definitions of the prediction, induced loss, and Hedge loss gives the claimed inequality.

**Key facts.** `hedgeDist_nonneg`, `hedgeDist_sum`.
