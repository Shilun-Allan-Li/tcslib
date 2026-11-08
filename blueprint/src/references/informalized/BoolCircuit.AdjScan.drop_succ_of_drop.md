<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformScan.lean :: BoolCircuit.AdjScan.drop_succ_of_drop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successive list drops

**Claim.** If dropping the first $p$ bits of $E$ gives a bit $b$ followed by $r$, then dropping the first $p+1$ bits gives $r$.

**Proof.** Dropping $p+1$ entries is the same as first dropping $p$ entries and then dropping one more. The first drop leaves $b$ followed by $r$, so the additional drop removes $b$ and leaves $r$.
