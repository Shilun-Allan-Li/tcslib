<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Comparison.lean :: CommunicationComplexity.PublicCoin.Protocol.toDeterministic_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fixing the Shared Randomness

**Claim.** For any public-coin protocol, fixing the shared random outcome to $\omega$ gives a deterministic protocol whose output on $(x,y)$ agrees with the randomized run using that same outcome.

**Proof.** By definition, the deterministic protocol is obtained by precomposing each party’s input with the map that pairs it with $\omega$. Unfolding this construction and the definition of randomized execution shows that running it on $x$ and $y$ evaluates the original protocol on $(\omega,x)$ and $(\omega,y)$, exactly the randomized run with coin outcome $\omega$.
