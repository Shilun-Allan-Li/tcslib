<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomBits.lean :: Randomized.randProb_append_ge -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lower Bound for Appended-Event Probability

**Claim.** If every prefix satisfying $A$ has conditional suffix-event probability at least $\varepsilon$, then the probability of the corresponding event on a uniformly chosen concatenated string is at least $P_{m_1}(A)\varepsilon$.

**Proof.** Split each length-$(m_1+m_2)$ string into its length-$m_1$ prefix and length-$m_2$ suffix. Counting through this bijection expresses the event's probability as the sum, over all prefixes, of their suffix-event probabilities, divided by $2^{m_1}$. Restrict this sum to prefixes satisfying $A$; the omitted terms are nonnegative because they are probabilities. Each retained term is at least $\varepsilon$ by hypothesis. Their sum is therefore at least $\varepsilon$ times the number of prefixes satisfying $A$. Dividing by $2^{m_1}$ gives $P_{m_1}(A)\varepsilon$.

**Key facts.** `Randomized.randProb_nonneg`.
