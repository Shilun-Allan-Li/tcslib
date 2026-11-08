<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/MatchingMath.lean :: Randomized.Matching.lovasz_test -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Randomized Determinant Test

**Claim.** Under the stated size and injectivity hypotheses, the random Lovász matrix has nonzero determinant with probability at least $1/2$.

**Proof.** First compare the event for a uniformly random word of length $m$ with the event obtained by truncating that word to its first $n^2k$ bits. These events agree because every sampled matrix entry uses a block lying within those first $n^2k$ bits (Randomized.Matching.lovaszSample_take); equality of events preserves their probabilities (Randomized.randProb_congr). The probability of the truncated event equals the probability for a uniformly random word of exactly $n^2k$ bits, since the event depends only on that prefix (Randomized.randProb_take). Finally apply the exact-length determinant-test bound, which gives probability at least $1/2$ under the perfect-matching, sample-size, and injectivity assumptions (Randomized.Matching.lovasz_test_exact).

**Key facts.** `Randomized.Matching.lovaszSample_take`, `Randomized.Matching.lovasz_test_exact`, `Randomized.randProb_congr`, `Randomized.randProb_take`.
