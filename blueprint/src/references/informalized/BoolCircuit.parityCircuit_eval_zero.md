<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Parity.lean :: BoolCircuit.parityCircuit_eval_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero-variable parity

**Claim.** The parity circuit on zero variables evaluates to false under the unique assignment of Boolean values to the zero variables.

**Proof.** The evaluation theorem for the parity circuit (`parityCircuit_eval`) identifies its value with the XOR-fold of the input bits over `List.finRange 0`, starting from false. This list is empty, so the fold is its initial value, false.

**Key facts.** `BoolCircuit.parityCircuit_eval`.
