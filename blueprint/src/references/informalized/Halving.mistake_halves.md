<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/MistakeBounds/Halving.lean :: Halving.mistake_halves -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Mistake Halves the Version Space

**Claim.** Whenever the Halving prediction is wrong, the updated version space has at most half as many hypotheses as the original version space.

**Proof.** The proof considers the two possible true labels. If the true label is false, a mistake means the algorithm predicted true, so the true-vote count is at least the false-vote count. The false-vote hypotheses are precisely the updated version space; since the two vote counts partition the original space (`Halving.voteFor_false_add_true`), twice the updated count is at most the original count. If the true label is true, a mistake means the algorithm predicted false, so the true-vote count is strictly less than the false-vote count. The update keeps the true-vote hypotheses, and the same partition identity again shows that twice this count is at most the original count. Thus the claim holds for either label.

**Key facts.** `Halving.voteFor_false_add_true`.
