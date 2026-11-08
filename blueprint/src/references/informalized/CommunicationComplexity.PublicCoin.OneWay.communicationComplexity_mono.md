<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/PublicCoinOneWay.lean :: CommunicationComplexity.PublicCoin.OneWay.communicationComplexity_mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity in Error Tolerance

**Claim.** If $\varepsilon'\leq\varepsilon$, then the public-coin communication complexity at tolerance $\varepsilon$ is at most that at tolerance $\varepsilon'$.

**Proof.** If the complexity at tolerance $\varepsilon'$ is infinite, the desired inequality follows because every element of $\mathbb{N}_\infty$ is at most infinity. Otherwise it equals some natural number $m$. By the upper-bound characterisation (`communicationComplexity_le_iff`), there is a protocol of some tape length that achieves error at most $\varepsilon'$ and has cost at most $m$. For every input pair, its failure probability is then at most $\varepsilon'$, hence at most $\varepsilon$. The same protocol and cost bound therefore witness, again by the characterisation, that the complexity at tolerance $\varepsilon$ is at most $m$, as required.

**Key facts.** `CommunicationComplexity.PublicCoin.OneWay.communicationComplexity_le_iff`.
