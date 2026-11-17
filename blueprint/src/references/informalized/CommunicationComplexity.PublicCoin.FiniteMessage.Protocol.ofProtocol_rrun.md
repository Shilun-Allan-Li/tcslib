<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/PublicCoinFiniteMessage.lean :: CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.ofProtocol_rrun -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Embedding preserves randomized execution

**Claim.** The finite-message embedding of a binary public-coin protocol has the same randomized output as the original protocol on every private input and shared random string.

**Proof.** Both randomized executions are deterministic runs on the same paired inputs $(\omega,x)$ and $(\omega,y)$. The deterministic embedding execution law says that the embedded protocol’s run on any fixed pair of inputs equals the original protocol’s run there (\texttt{CommunicationComplexity.Deterministic.FiniteMessage.Protocol.ofProtocol\_run}). Applying this law to the paired inputs gives the stated equality.

**Key facts.** `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.ofProtocol_run`.
