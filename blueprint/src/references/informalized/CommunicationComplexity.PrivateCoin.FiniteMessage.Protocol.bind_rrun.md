<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/PrivateCoinComposition.lean :: CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol.bind_rrun -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Execution of Sequential Composition

**Claim.** Executing the sequential composition of protocols $p$ and $q$ with fixed inputs and private coins gives the same output as running $p$ first and then running the protocol selected by its output with those same inputs and coins.

**Proof.** The deterministic execution law for sequential composition states that $(p\bind q)$ run on inputs $u,v$ equals $q(p\text{ run on }u,v)$ run on $u,v$ (`CommunicationComplexity.Deterministic.FiniteMessage.Protocol.bind_run`). Apply it to the paired inputs $u=(\omega_x,x)$ and $v=(\omega_y,y)$. By the definition of private-coin execution, the resulting equality is precisely the claimed identity.

**Key facts.** `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.bind_run`.
