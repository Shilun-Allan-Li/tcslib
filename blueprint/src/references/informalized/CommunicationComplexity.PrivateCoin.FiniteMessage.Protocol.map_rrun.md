<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/PrivateCoinComposition.lean :: CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol.map_rrun -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Execution Commutes with Output Mapping

**Claim.** Executing the protocol obtained by mapping the output of $p$ by $g$ yields $g$ applied to the output of executing $p$ with the same inputs and private coins.

**Proof.** For deterministic protocols, mapping the output commutes with execution: $(p.map\,g)$ run on $u,v$ equals $g$ of the output of $p$ run on $u,v$ (`CommunicationComplexity.Deterministic.FiniteMessage.Protocol.map_run`). Use the paired inputs $u=(\omega_x,x)$ and $v=(\omega_y,y)$, then express both sides as private-coin executions to obtain the result.

**Key facts.** `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.map_run`.
