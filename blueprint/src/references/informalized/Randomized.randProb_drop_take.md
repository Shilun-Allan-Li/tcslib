<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomBits.lean :: Randomized.randProb_drop_take -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Probability of a Word Segment

**Claim.** If $s+T\le m$, then the probability that the length-$T$ segment obtained by dropping the first $s$ bits of a uniformly random length-$m$ word satisfies $B$ equals the probability that a uniformly random length-$T$ word satisfies $B$.

**Proof.** First, the event depends only on the first $s+T$ bits: truncating the random word to that length leaves the segment unchanged, since $s+T\le m$. The probability is therefore the same as for words of length $s+T$, by the fact that events determined by an initial segment have the same probability as on that segment (`Randomized.randProb_take`). On a word of length $s+T$, add the vacuous condition that its first $s$ bits satisfy the constantly true predicate. The split rule factors the probability into the probability of that prefix condition and the probability that the remaining length-$T$ block, truncated to length $T$, satisfies $B$ (`Randomized.randProb_split`). The prefix factor is one (`Randomized.randProb_true`); the block has length $T$, so truncating it to length $T$ leaves it unchanged. Thus the resulting probability is precisely that of $B$ on a uniform length-$T$ word.

**Key facts.** `Randomized.randProb_take`, `Randomized.randProb_congr`, `Randomized.randProb_split`, `Randomized.randProb_true`.
