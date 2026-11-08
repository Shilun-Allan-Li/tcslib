<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/BalancedSimulation.lean :: CommunicationComplexity.Deterministic.Protocol.max_sq_le_of_balanced -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Squared bound for a balanced split

**Claim.** If $3m\le 2n$ and $3(n-m)\le 2n$, then $9\max(m^2,(n-m)^2)\le 4n^2$.

**Proof.** Squaring the first nonnegative inequality gives $(3m)^2\le(2n)^2$, hence $9m^2\le4n^2$. Squaring the second gives $9(n-m)^2\le4n^2$. The maximum of these two squares is one of them: if $m^2\le(n-m)^2$, use the second bound; otherwise use the first. In either case, multiplying the selected inequality by the required coefficient is already incorporated in the displayed bounds, and gives the claim.
