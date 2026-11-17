<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/PrivateCoinFiniteMessage.lean :: CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol.rrun_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Explicit-Coin Execution

**Claim.** Executing a private-coin protocol with specified coins agrees with running its underlying deterministic protocol on the corresponding paired coin-inputs.

**Proof.** By definition, private-coin execution on $(x,y)$ with coins $(\omega_x,\omega_y)$ is the underlying deterministic run at inputs $(\omega_x,x)$ and $(\omega_y,y)$. Thus the two expressions are identical.
