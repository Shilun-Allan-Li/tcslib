<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/PublicCoinComplexity.lean :: CommunicationComplexity.PublicCoin.communicationComplexity_le_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complexity as an Achievable Bound

**Claim.** The public-coin communication complexity is at most $m$ exactly when some coin-tape length and protocol $\varepsilon$-computing $f$ have communication complexity at most $m$.

**Proof.** Expand the definition of public-coin communication complexity as an iterated infimum over coin-tape lengths, protocols, and protocols satisfying the approximation condition. The infimum of an $\mathbb{N}_\infty$-valued family is at most the natural number $m$ exactly when some member of the family is at most $m$ (`enat_iInf_le_coe_iff`). Applying this fact successively to the nested infima gives a coin-tape length, a protocol, and an approximation witness whose complexity is at most $m$. Unpacking the witness yields the stated characterization.

**Key facts.** `CommunicationComplexity.Internal.enat_iInf_le_coe_iff`.
