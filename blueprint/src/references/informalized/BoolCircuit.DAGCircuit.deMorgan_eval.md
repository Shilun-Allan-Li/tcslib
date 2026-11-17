<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGFanin.lean :: BoolCircuit.DAGCircuit.deMorgan_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation preserved by the De Morgan transformation

**Claim.** For every Boolean input assignment, the De Morgan transformed circuit has the same output as the original circuit.

**Proof.** The general rewrite evaluation theorem (`DAGCircuit.rewrite_eval`) states that a circuit rewritten using semantically correct gadgets has the same output on every input assignment. The De Morgan gadget correctness result supplies that semantic preservation, and the original circuit's well-formedness and argument bound satisfy the gadget hypotheses. Applying the rewrite evaluation theorem to this transformation gives the claimed equality.

**Key facts.** `BoolCircuit.DAGCircuit.rewrite_eval`.
