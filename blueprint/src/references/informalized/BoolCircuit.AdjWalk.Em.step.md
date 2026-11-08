<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformWalk.lean :: BoolCircuit.AdjWalk.Em.step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Step Predecessor for Emission

**Claim.** If all registers of $a$ are at most $B$, and the configuration after one step of the walk satisfies the emission property for a segment starting at $k$ with postcondition $P$, then $a$ satisfies that property as well.

**Proof.** The register bound on $a$ makes the one-step transition from $a$ to its successor a bounded reach (`Complexity.LogProg.AReach.single`). Apply the prepend-reach principle (`BoolCircuit.AdjWalk.Em.pre`) to this reach and the assumed emission property of the successor. The result is the emission property from $a$.

**Key facts.** `BoolCircuit.AdjWalk.Em.pre`, `Complexity.LogProg.AReach.single`.
