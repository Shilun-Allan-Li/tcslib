<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/PublicCoinOneWay.lean :: CommunicationComplexity.PublicCoin.OneWay.communicationComplexity_le_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Upper-Bound Characterisation

**Claim.** The public-coin communication complexity of $f$ at error tolerance $\varepsilon$ is at most $m$ exactly when some coin-tape length and protocol at that length both achieve error at most $\varepsilon$ and have bit cost at most $m$.

**Proof.** Unfold the definition of communication complexity as an iterated infimum in $\mathbb{N}_\infty$. The fact that an infimum in $\mathbb{N}_\infty$ is at most the natural number $m$ exactly when some index has value at most $m$ (`enat_iInf_le_coe_iff`) turns the outer infimum over tape lengths into an existential choice of a length. Applying the same fact to the infimum over protocols and then over protocols satisfying the error condition gives a protocol and its error witness whose cost is at most $m$. Reassembling the error witness yields the stated conjunction. These transformations are equivalences, so they also prove the converse.

**Key facts.** `CommunicationComplexity.Internal.enat_iInf_le_coe_iff`.
