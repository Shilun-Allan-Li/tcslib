<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyConfigCircuit.lean :: Complexity.cfgCircuit_isFaninTwo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Configuration circuit fan-in

**Claim.** For every finite-state binary Turing machine $M$, natural number $n$, finite list of bit sources $\ell$, and time bound $T$, the configuration circuit built from these data is well formed and every gate reads at most two vertices.

**Proof.** The configuration circuit is a particular program circuit: it uses the instruction list for the configuration computation, with the output chosen at the snapshot position for time $T$. The general fan-in theorem for program circuits states that every such circuit is well formed and each of its gates has at most two arguments (`BoolCircuit.progCircuit_isFaninTwo`). Applying it to this program circuit gives the assertion.

**Key facts.** `BoolCircuit.progCircuit_isFaninTwo`.
