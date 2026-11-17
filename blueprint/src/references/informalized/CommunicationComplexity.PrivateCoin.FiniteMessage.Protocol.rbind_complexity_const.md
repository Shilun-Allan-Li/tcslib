<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/PrivateCoinComposition.lean :: CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol.rbind_complexity_const -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complexity of Fresh-Randomness Bind

**Claim.** If every continuation protocol has complexity $c$, then running $p$ followed by the selected continuation with fresh randomness has complexity $\mathrm{complexity}(p)+c$.

**Proof.** The fresh-randomness bind is defined by first reindexing each party’s input so that the first coin coordinate is used by $p$, then binding the result to a continuation reindexed to use the second coin coordinate. Reindexing inputs does not change the protocol’s communication tree or its complexity. The deterministic bind complexity theorem says that binding a protocol to continuations all of complexity $c$ adds exactly $c$ to the original complexity (`CommunicationComplexity.Deterministic.FiniteMessage.Protocol.bind_complexity_const`). Applying it to these reindexed protocols gives the claimed sum.

**Key facts.** `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.bind_complexity_const`.
