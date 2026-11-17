<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/PublicCoinComplexity.lean :: CommunicationComplexity.PublicCoin.le_communicationComplexity_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lower-Bound Characterization

**Claim.** The natural number $m$ is at most the public-coin communication complexity if and only if every $\varepsilon$-computing protocol on every coin-tape length has complexity at least $m$.

**Proof.** Expand the communication complexity as the infimum over coin-tape lengths, protocols, and approximation witnesses. In an ordered set, an element is at most an infimum exactly when it is at most every member of the family. Applying this characterization to the nested infima, and using that comparison of natural numbers viewed in $\mathbb{N}_\infty$ agrees with their usual order, gives precisely the universal statement over lengths and protocols with their approximation hypotheses.
