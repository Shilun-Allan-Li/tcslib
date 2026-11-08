<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Hedge/Basic.lean :: hedgeWeight_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive Hedge Weights

**Claim.** Every unnormalized Hedge weight is strictly positive.

**Proof.** The weight is the exponential of the real number given by the negative learning rate times cumulative loss. The real exponential is strictly positive at every real input, so the weight is strictly positive.
