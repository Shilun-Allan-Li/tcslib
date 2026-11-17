<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/PublicCoinComplexity.lean :: CommunicationComplexity.PublicCoin.communicationComplexity_mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity in the Error Tolerance

**Claim.** If $\varepsilon'\le\varepsilon$, then the public-coin communication complexity at error tolerance $\varepsilon$ is at most that at tolerance $\varepsilon'$.

**Proof.** If the complexity at tolerance $\varepsilon'$ is infinite, the desired inequality holds because every value is at most infinity. Otherwise, let its value be the natural number $m$. The bound characterization (`communicationComplexity_le_iff`) gives a coin-tape protocol of complexity at most $m$ whose error on every input is at most $\varepsilon'$. Since $\varepsilon'\le\varepsilon$, the same protocol also meets the larger error tolerance. Applying the characterization again shows that the complexity at tolerance $\varepsilon$ is at most $m$, as required.

**Key facts.** `CommunicationComplexity.PublicCoin.communicationComplexity_le_iff`.
