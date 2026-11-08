<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/LearningConsequences.lean :: FABL.singletonInfluenceAccuracy_le_quarter_threshold -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Singleton Accuracy Threshold Bound

**Claim.** The singleton influence accuracy is at most one quarter of the learning consequences threshold.

**Proof.** By definition, the accuracy parameter is the minimum of one quarter of the threshold and $1/2$. A minimum is at most each of its arguments, so it is at most one quarter of the threshold.
