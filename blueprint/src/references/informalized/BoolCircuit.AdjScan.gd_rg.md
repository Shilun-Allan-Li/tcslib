<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformScan.lean :: BoolCircuit.AdjScan.gd_rg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Register Bound for a Triple

**Claim.** If each of $p,c,a$ is at most $B$, then every register in the configuration whose register triple is $(p,c,a)$ is at most $B$, regardless of its control state or answer status.

**Proof.** A register index in a triple has one of three possible values. The first, second, and third register values are $p$, $c$, and $a$, respectively, by the definition of the register triple. Each is at most $B$ by hypothesis, so every register satisfies the required bound.

**Key facts.** `BoolCircuit.AdjScan.fin3_cases`.
