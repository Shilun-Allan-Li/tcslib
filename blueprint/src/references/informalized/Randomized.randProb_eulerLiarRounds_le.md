<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PrimalityMath.lean :: Randomized.randProb_eulerLiarRounds_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Repeated Euler Liar Probability Bound

**Claim.** For odd composite $N>1$, the probability that all $k$ Euler liar rounds accept, using $\ell k$ random bits in blocks of length $\ell$, is at most $\left(\frac12+\frac{N-1}{2^{\ell+1}}\right)^k$.

**Proof.** Proceed by induction on the number $k$ of rounds. With zero rounds, acceptance is certain, and its probability is at most one (`Randomized.randProb_le_one`), the claimed bound for the zeroth power. For the induction step, write the total length as $\ell+\ell k$. Acceptance means that the candidate formed from the first block is an Euler liar and that the remaining $k$ rounds accept on the suffix. The block-splitting rule makes the probability of this conjunction the product of the one-round liar probability and the $k$-round acceptance probability (`Randomized.randProb_split`); the equivalence with the actual round definition follows directly from its recursive clause (`Randomized.randProb_congr`). The one-round probability is at most $\frac12+\frac{N-1}{2^{\ell+1}}$ (`Randomized.randProb_isEulerLiar_le`), and the induction hypothesis bounds the remaining factor by the $k$th power of the same quantity. Since probabilities are nonnegative, multiplying these inequalities gives the claimed $(k+1)$st-power bound.

**Key facts.** `Randomized.randProb_le_one`, `Randomized.randProb_congr`, `Randomized.randProb_split`, `Randomized.randProb_isEulerLiar_le`, `Randomized.randProb_nonneg`.
