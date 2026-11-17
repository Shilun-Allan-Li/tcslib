<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformWalk.lean :: BoolCircuit.AdjWalk.gd_rg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Register Bounds for the Tuple

**Claim.** If $k,V,U,W\le B$, then the configuration with registers $(k,V,U,W)$ has every register at most $B$.

**Proof.** An arbitrary register is one of the four coordinates. By exhaustion of the four registers (`fin4_cases`), it suffices to check each coordinate separately. The register tuple assigns them the values $k,V,U,W$, respectively, and each is at most $B$ by hypothesis.

**Key facts.** `BoolCircuit.AdjWalk.fin4_cases`.
