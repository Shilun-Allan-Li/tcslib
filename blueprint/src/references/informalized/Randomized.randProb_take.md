<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Classes.lean :: Randomized.randProb_take -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Probability of a prefix event

**Claim.** If $m_1\le m$, then the probability that the first $m_1$ entries of a uniformly random length-$m$ Boolean word satisfy $A$ equals the probability that a uniformly random length-$m_1$ word satisfies $A$.

**Proof.** Write $m=m_1+m_2$. The event depends only on the first $m_1$ entries, so it can be expressed as the conjunction of $A$ on the prefix and the always-true condition on the suffix; this changes no probability (`Randomized.randProb_congr`). The product rule (`Randomized.randProb_split`) makes this probability the product of the prefix probability and the probability of the always-true suffix. The latter is $1$ (`Randomized.randProb_true`), leaving the desired prefix probability.

**Key facts.** `Randomized.randProb_congr`, `Randomized.randProb_split`, `Randomized.randProb_true`.
