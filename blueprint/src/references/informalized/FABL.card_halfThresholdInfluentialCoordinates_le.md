<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/LearningConsequences.lean :: FABL.card_halfThresholdInfluentialCoordinates_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Half-threshold coordinate bound

**Claim.** Under the stated total-influence bound, the number of coordinates whose influence is at least half the learning threshold is at most the ceiling of twice the influence bound divided by that threshold.

**Proof.** Write $\theta$ for the learning threshold, which is positive (`learningConsequencesThreshold_pos`). The number of coordinates with influence at least $\theta/2$ is at most total influence divided by $\theta/2$ (`card_influentialCoordinates_le_div`). Using the assumed upper bound on total influence, this is at most $2t/\theta$. The ceiling of $2t/\theta$ is an integer upper bound for that real quantity, proving the claim.

**Key facts.** `FABL.learningConsequencesThreshold_pos`, `FABL.card_influentialCoordinates_le_div`.
