<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/PrivateCoinFiniteMessage.lean :: CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol.ofProtocol_rrun -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Execution preservation under embedding

**Claim.** Embedding a binary private-coin protocol into the finite-message framework preserves its output for every input pair and every pair of private coins.

**Proof.** By definition, randomized execution feeds the coin and input pairs $(\omega_x,x)$ and $(\omega_y,y)$ to the underlying deterministic protocol. The embedding preserves deterministic execution on every pair of arguments (`Deterministic.FiniteMessage.Protocol.ofProtocol_run`). Applying that result to these two paired arguments gives the claimed equality of randomized outputs.

**Key facts.** `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.ofProtocol_run`.
