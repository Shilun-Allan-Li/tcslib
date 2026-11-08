<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/DetBasic.lean :: CommunicationComplexity.Deterministic.Protocol.alice_to_bob -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Swapping an Alice-Rooted Protocol

**Claim.** Swapping the input roles of an Alice-rooted protocol yields a protocol on the reversed input types that computes the same outputs on reversed inputs and has the same communication complexity.

**Proof.** Take $q$ to be the role-swapped version of the Alice-rooted protocol. The swap-run identity says that running the swapped protocol on $(y,x)$ gives the same output as running the original protocol on $(x,y)$ (\texttt{swap\_run}). The swap-complexity identity says that the two protocols have equal communication complexity (\texttt{swap\_complexity}). These establish both required properties of $q$.

**Key facts.** `CommunicationComplexity.Deterministic.Protocol.swap_run`, `CommunicationComplexity.Deterministic.Protocol.swap_complexity`.
