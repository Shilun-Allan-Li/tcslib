<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/PrivateCoinFiniteMessage.lean :: CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol.ofProtocol_equiv -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finite-message simulation

**Claim.** Every binary private-coin protocol has a finite-message protocol with the same output on every input and coin choice, and with exactly the same communication complexity.

**Proof.** Take the finite-message protocol obtained by applying `ofProtocol` to $p$. The execution-preservation result (`ofProtocol_rrun`) says that, for every $x,y,\omega_x,\omega_y$, its output equals the output of $p$ on those data. The complexity-preservation result (`ofProtocol_complexity`) gives equality of their communication complexities. Together these establish both required properties of the chosen protocol.

**Key facts.** `CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol.ofProtocol_rrun`, `CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol.ofProtocol_complexity`.
