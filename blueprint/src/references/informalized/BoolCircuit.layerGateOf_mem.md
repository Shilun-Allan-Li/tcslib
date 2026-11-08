<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LayeredDAG.lean :: BoolCircuit.layerGateOf_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Standard Operation for a Layered Gate

**Claim.** The operation of the layered gate associated with a well-formed DAG gate belongs to the standard set of identity, NOT, and arbitrary-fanin AND operations.

**Proof.** Consider the gate-kind cases in the construction. For a NOT gate, the operation is the unary map $z\mapsto 1-z$, which is one of the listed standard operations. For an AND gate, the operation is the product over a finite set of inputs, so it belongs to the arbitrary-fanin AND family. The OR-kind case uses the same product operation in this construction and therefore belongs to that family as well.
