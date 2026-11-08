<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Hedge/Episode.lean :: episodeLossSeq_valid -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Validity of Episode Losses

**Claim.** Every loss in the generated episode loss sequence lies between $0$ and $1$.

**Proof.** Fix a round and an expert, and expand the episode loss sequence at that round using its definition. Unfolding the recursive episode loss at the selected round shows that this value is the adversary's loss for the history of previously generated losses and the learner's strategy chosen from that history. The adversary's validity condition states that each such loss coordinate lies between $0$ and $1$, proving the claim.
