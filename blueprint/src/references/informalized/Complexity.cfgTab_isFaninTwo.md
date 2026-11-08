<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauSpec.lean :: Complexity.cfgTab_isFaninTwo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Configuration Tableau Fan-In Bound

**Claim.** The configuration tableau circuit is well formed, and every gate in it reads at most two vertices.

**Proof.** The configuration tableau is an instance of the general tableau circuit construction, with the configuration program and its chosen output indices. The theorem that every tableau circuit is well formed and has gates of fan-in at most two (`BoolCircuit.tabCircuit_isFaninTwo`) applies directly, yielding the claim.

**Key facts.** `BoolCircuit.tabCircuit_isFaninTwo`.
