<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/PublicCoinFiniteMessage.lean :: CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.rrun_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Randomized execution as deterministic execution

**Claim.** For a public-coin finite-message protocol, its execution on inputs $x,y$ with shared randomness $\omega$ is its deterministic execution on the effective inputs $(\omega,x)$ and $(\omega,y)$.

**Proof.** By definition, randomized execution applies the protocol's deterministic execution to $(\omega,x)$ and $(\omega,y)$. The two sides are therefore identical by unfolding the definition.
