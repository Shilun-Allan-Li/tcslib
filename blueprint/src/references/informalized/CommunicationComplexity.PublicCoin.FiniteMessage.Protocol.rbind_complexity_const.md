<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/PublicCoinComposition.lean :: CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.rbind_complexity_const -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complexity of a Fresh-Randomness Bind

**Claim.** If every continuation in a fresh-randomness bind has complexity $c$, then the bound protocol has complexity equal to the initial protocol’s complexity plus $c$.

**Proof.** Unfold the fresh-randomness bind as an ordinary deterministic bind after reindexing the inputs: the initial protocol receives the first randomness coordinate, while each selected continuation receives the second. These changes of input coordinates preserve complexity. Each continuation therefore still has complexity $c$, as assumed. Applying the constant-continuation bind theorem adds this common continuation cost to the initial protocol’s complexity (`CommunicationComplexity.Deterministic.FiniteMessage.Protocol.bind_complexity_const`).

**Key facts.** `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.bind_complexity_const`.
