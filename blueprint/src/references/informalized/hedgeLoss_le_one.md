<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Hedge/Basic.lean :: hedgeLoss_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Hedge Expected Loss Bound

**Claim.** If every expert's loss lies in $[0,1]$, then the learner's expected loss under the Hedge distribution at each round is at most $1$.

**Proof.** For each expert, its loss is at most $1$. Multiplying this inequality by that expert's nonnegative Hedge probability preserves the inequality. Summing over experts bounds the learner's expected loss by the sum of the probabilities, which is $1$ by normalization.

**Key facts.** `hedgeDist_nonneg`, `hedgeDist_sum`.
