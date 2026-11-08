<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitTreeManip.lean :: LMN.TreeCircuit.depth0_is_lit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth-zero circuits are literals

**Claim.** A Boolean circuit tree of depth zero consists of a single literal.

**Proof.** Inspect the outer constructor of the circuit. If it is a literal, that literal itself gives the required representation. If it is a node, its depth is one plus a nonnegative quantity, hence at least one, contradicting the assumed depth zero. Therefore only the literal case is possible.
