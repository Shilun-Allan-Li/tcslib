<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/MistakeBounds/Halving.lean :: Halving.voteFor_false_add_true -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Vote Counts Partition the Version Space

**Claim.** The numbers of hypotheses in $V$ predicting false and true on a fixed input sum to $|V|$.

**Proof.** The false-voting hypotheses are filtered from $V$ by the condition that the prediction is false. Because every prediction is Boolean, predicting true is equivalent to not predicting false. Thus the true-voting set is the complementary filter within $V$. The cardinalities of a filtered set and its complement sum to the cardinality of the whole finite set, giving the identity.
