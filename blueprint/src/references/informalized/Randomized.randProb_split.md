<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Classes.lean :: Randomized.randProb_split -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product rule for word events

**Claim.** For independent uniformly random Boolean words of lengths $m_1$ and $m_2$, the probability that the first satisfies $A$ and the second satisfies $B$ is the product of the two individual probabilities.

**Proof.** A word of length $m_1+m_2$ is uniquely obtained by concatenating a word of length $m_1$ with one of length $m_2$. Under this correspondence, its prefix and suffix are exactly those two words, so the words satisfying the combined event correspond bijectively to pairs whose first component satisfies $A$ and whose second satisfies $B$. Thus the number of successful words is the product of the two separate counts. Dividing by the total number $2^{m_1+m_2}=2^{m_1}2^{m_2}$ gives the stated product of probabilities.
