<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/PublicCoinOneWay.lean :: CommunicationComplexity.PublicCoin.OneWay.le_communicationComplexity_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lower-Bound Characterisation

**Claim.** The natural number $m$ is at most the public-coin communication complexity at tolerance $\varepsilon$ exactly when every protocol at every coin-tape length that achieves that tolerance has cost at least $m$.

**Proof.** Unfold the complexity as an iterated infimum of protocol costs in $\mathbb{N}_\infty$. Being below an infimum is equivalent to being below every value indexed by it (`le_iInf_iff`). Apply this successively to the infimum over tape lengths, protocols, and protocols satisfying the error condition. Since the lower bound is a natural number, comparing it with each cost cast into $\mathbb{N}_\infty$ is equivalent to the natural-number inequality. The resulting statement says exactly that every qualifying protocol has cost at least $m$.
