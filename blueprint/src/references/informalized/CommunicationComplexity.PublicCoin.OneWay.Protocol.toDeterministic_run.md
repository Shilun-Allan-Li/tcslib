<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/OneWayMinimax.lean :: CommunicationComplexity.PublicCoin.OneWay.Protocol.toDeterministic_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fixing the Public Coin

**Claim.** Fixing the public coin at any outcome turns a one-way public-coin protocol into a deterministic protocol whose output on inputs $x,y$ is the randomized run of the original protocol with that coin outcome.

**Proof.** By definition, the fixed-coin protocol sends the message that the original encoder assigns to $(\omega,x)$ and decodes that message using Bob's paired input $(\omega,y)$. Its deterministic run is therefore $p.\mathrm{decode}(p.\mathrm{send}(\omega,x), (\omega,y))$, which is exactly the definition of the randomized run at $\omega$.
