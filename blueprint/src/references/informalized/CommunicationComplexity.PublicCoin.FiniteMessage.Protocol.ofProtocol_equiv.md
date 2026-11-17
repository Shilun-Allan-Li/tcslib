<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/PublicCoinFiniteMessage.lean :: CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.ofProtocol_equiv -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finite-message representation of public-coin protocols

**Claim.** Every public-coin protocol has a finite-message protocol with the same randomized outputs on every input and shared random string, and with the same communication complexity.

**Proof.** Choose the finite-message embedding of the given protocol. The embedding preserves randomized execution, so its output agrees with the original protocol for every private input and shared random string (\texttt{CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.ofProtocol\_rrun}). Its complexity is also preserved by the embedding complexity theorem (\texttt{CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.ofProtocol\_complexity}). These two properties establish the required existence.

**Key facts.** `CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.ofProtocol_rrun`, `CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.ofProtocol_complexity`.
