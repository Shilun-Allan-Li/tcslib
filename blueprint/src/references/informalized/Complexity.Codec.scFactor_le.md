<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Machine.lean :: Complexity.Codec.scFactor_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Upper bound for scan factors

**Claim.** For every scan identifier, its scan factor is at most four times the encoding width.

**Proof.** The width $W$ is at least $1$. Split into the six possible scan identifiers. For $E$ and $E2$, the factor is exactly $4W$. For $F$, $F2$, and $In$, it is $2$, which is at most $4W$ since $W\ge1$. For $C$, it is $2W$, also at most $4W$.
