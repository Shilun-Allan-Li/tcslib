<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitTreeManip.lean :: LMN.TreeCircuit.exists_node_of_depth_ge_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive depth gives a gate

**Claim.** A circuit tree of depth at least $1$ is a node formed from some gate type and a list of child circuits.

**Proof.** Inspect the outer form of the circuit. If it is a literal, its depth is $0$, contradicting the assumed lower bound. Therefore it must be a node, and its gate type and child list provide the required representation.
