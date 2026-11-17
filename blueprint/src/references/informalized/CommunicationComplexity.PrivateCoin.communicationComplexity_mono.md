<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/PrivateCoinComplexity.lean :: CommunicationComplexity.PrivateCoin.communicationComplexity_mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity in the error bound

**Claim.** If $\varepsilon'\leq\varepsilon$, then the private-coin complexity at error $\varepsilon$ is at most the complexity at error $\varepsilon'$.

**Proof.** If the complexity at error $\varepsilon'$ is infinite, the result follows from the fact that every extended natural number is at most infinity. Otherwise, let its value be the natural number $m$. The upper-bound characterization supplies a protocol with some coin-tape lengths, error at most $\varepsilon'$, and cost at most $m$. The same protocol has error at most $\varepsilon$, since its error bound is at most $\varepsilon'$ and $\varepsilon'\leq\varepsilon$. The characterization at error $\varepsilon$ therefore gives complexity at most $m$, which is the original complexity.

**Key facts.** `CommunicationComplexity.PrivateCoin.communicationComplexity_le_iff`.
