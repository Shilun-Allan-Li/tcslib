<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Hedge/ConvexPrediction.lean :: hedgePredictionCumLoss_le_hedgeCumLoss -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cumulative Jensen Bound

**Claim.** The cumulative loss of Hedge’s weighted-average predictions is at most the cumulative Hedge loss on the induced loss sequence.

**Proof.** Fix a round. The one-round Jensen bound for Hedge’s prediction (`hedgePrediction_loss_le_hedgeLoss`) says that the loss of the weighted-average prediction is at most the Hedge-weighted average of the experts’ induced losses. Sum this inequality over all rounds; termwise order is preserved by finite summation, yielding the stated cumulative bound.

**Key facts.** `hedgePrediction_loss_le_hedgeLoss`.
