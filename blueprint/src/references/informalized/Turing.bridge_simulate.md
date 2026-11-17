<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/MathlibBridge.lean :: Turing.bridge_simulate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Simulation of Compiled Runs

**Claim.** If compiled configuration $b$ is reachable from $a$, and $a$’s label lies in the compilation’s label support with halt adjoined, then $b$’s label also lies there, and the bridging machine reaches the bridge configuration for $b$ from that for $a$, preserving the input-head position and output word.

**Proof.** Induct on the compiled reachability derivation. In the reflexive case, the endpoint is $a$ itself, so its label retains the assumed support membership and the bridge configurations are related by reflexive reachability (`bridgeReach_refl`). For a reachability extended by one compiled step, the support invariant for compiled steps ensures that the new label remains in the label support with halt adjoined. By the induction hypothesis, the bridge machine already reaches the bridge configuration for the intermediate configuration. If its label is absent, the compiled step is stationary. Otherwise, the compiled step is the transition determined by that label and register. The translated label is in the statement support by the translated-label fact (`bridge_label`), so the one-statement simulation applies (`bridge_statement`) to reach the bridge configuration for the next compiled configuration. Concatenate this with the inductive reach using transitivity (`bridgeReach_trans`).

**Key facts.** `Turing.bridgeReach_refl`, `Turing.bridgeReach_trans`, `Turing.bridge_label`, `Turing.bridge_statement`.
