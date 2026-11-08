<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Hedge/Basic.lean :: hedgeLoss_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegative Hedge Loss

**Claim.** For a valid loss sequence and any round, Hedge’s expected loss is nonnegative.

**Proof.** The expected loss is a finite sum whose $i$th term is the product of expert $i$’s Hedge probability and that expert’s loss. The probability is nonnegative by the nonnegativity of the Hedge distribution (`hedgeDist_nonneg`), and the loss is nonnegative by validity of the sequence. Each product is therefore nonnegative, so their sum is nonnegative.

**Key facts.** `hedgeDist_nonneg`.
