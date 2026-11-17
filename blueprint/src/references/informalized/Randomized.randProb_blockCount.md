<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Classes.lean :: Randomized.randProb_blockCount -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binomial Distribution of Successful Blocks

**Claim.** For $j\le K$, the probability that exactly $j$ of the $K$ consecutive length-$q$ blocks pass $B$ is $\binom Kj s^j(1-s)^{K-j}$, where $s$ is the probability that $B$ passes on a uniform length-$q$ string.

**Proof.** Proceed by induction on the number of blocks, splitting off the first block. With zero blocks, the count is zero with probability one, while every positive count is impossible. For $K+1$ blocks and count zero, the first block must fail and the remaining $K$ blocks must also have count zero. The probability of these independent conditions multiplies by the block-splitting formula (`Randomized.randProb_split`); the probability of failure is $1-s$ (`Randomized.randProb_bool_false`). The induction hypothesis then gives $(1-s)^{K+1}$.

For $K+1$ blocks and count $j+1$, there are two disjoint possibilities: the first block passes and the remaining blocks have count $j$, or the first block fails and the remaining blocks have count $j+1$. The block-count recursion (`Randomized.blockCount_succ`) gives this decomposition, and the two cases are disjoint because the first block cannot both pass and fail. Add their probabilities (`Randomized.randProb_or_disjoint`), and factor each by the block-splitting formula. If $j<K$, the induction hypotheses for counts $j$ and $j+1$ apply. Pascal's identity for binomial coefficients combines the two terms into the claimed formula, with the exponent relation $K-j=(K-j-1)+1$ accounting for the additional failure factor. If $j=K$, the second term would require $K+1$ successful blocks among only $K$ remaining blocks, so it has probability zero: the count is at most the number of blocks (`Randomized.blockCount_le`), and an impossible event has probability zero (`Randomized.randProb_false`). The first term then gives the formula using $\binom{K+1}{K+1}=1$.

**Key facts.** `Randomized.blockCount_succ`, `Randomized.randProb_split`, `Randomized.randProb_bool_false`, `Randomized.randProb_or_disjoint`, `Randomized.blockCount_le`, `Randomized.randProb_false`.
