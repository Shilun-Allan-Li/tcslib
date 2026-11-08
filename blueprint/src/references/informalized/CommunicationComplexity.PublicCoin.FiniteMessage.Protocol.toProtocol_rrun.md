<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/PublicCoinFiniteMessage.lean :: CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.toProtocol_rrun -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Execution preserved by binary conversion

**Claim.** For every pair of private inputs and every shared-randomness outcome, the binary public-coin protocol obtained by converting a finite-message protocol returns the same output as the original protocol.

**Proof.** The converted binary protocol is chosen so that its deterministic execution agrees with that of the original finite-message protocol on every effective input (`Deterministic.FiniteMessage.Protocol.toProtocol_run`). Apply this equality to the effective inputs $(\omega,x)$ and $(\omega,y)$. By the definitions of public-coin execution, the resulting equality is exactly the claimed agreement of randomized executions.

**Key facts.** `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.toProtocol_run`.
