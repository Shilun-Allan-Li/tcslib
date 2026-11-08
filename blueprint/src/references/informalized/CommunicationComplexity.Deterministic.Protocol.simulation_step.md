<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/BalancedSimulation.lean :: CommunicationComplexity.Deterministic.Protocol.simulation_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Simulation by testing a subprotocol

**Claim.** The protocol that tests Alice's and Bob's reachability of a proper subprotocol, runs the input simulation when both tests succeed, and otherwise runs the pruned simulation computes the same function as the original protocol.

**Proof.** Fix inputs $(x,y)$ and split into whether they reach the subprotocol. If they do, the testing protocol runs $q_{\mathrm{in}}$ (`testSubprotocol_run_inside`), which computes the same function as $s$ by hypothesis. On inputs reaching $s$, the original protocol and $s$ agree (`subprotocol_run_eq_of_reaches`), so the testing protocol's output equals the original output. If the inputs do not reach $s$, the testing protocol runs $q_{\mathrm{out}}$ (`testSubprotocol_run_outside`). This agrees with the pruned protocol by hypothesis, and pruning preserves the original output outside the subprotocol (`prune_run_outside_of_lt`). Both cases establish equality on every input pair.

**Key facts.** `CommunicationComplexity.Deterministic.Protocol.testSubprotocol_run_inside`, `CommunicationComplexity.Deterministic.Protocol.subprotocol_run_eq_of_reaches`, `CommunicationComplexity.Deterministic.Protocol.testSubprotocol_run_outside`, `CommunicationComplexity.Deterministic.Protocol.prune_run_outside_of_lt`.
