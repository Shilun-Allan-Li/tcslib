<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.comp_power_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Power and Factor Bounds

**Claim.** If $b\le n+1$ and $r\le e+1$, then both $b^r$ and $F b^r$ are bounded by $8(2C+3)(n+1)^{e+1}$, where $F=2C+3$ when $o$ is true and $F=C$ otherwise.

**Proof.** Monotonicity of natural-number powers in the base gives $b^r\le(n+1)^r$. Since $n+1\ge1$ and $r\le e+1$, monotonicity in the exponent then gives $(n+1)^r\le(n+1)^{e+1}$. The coefficient $8(2C+3)$ is positive and at least $1$, so this bounds $b^r$ by the claimed expression. In either Boolean case, $F\le8(2C+3)$: for the true case this is immediate, and for the false case $F=C\le 8(2C+3)$. Multiplying this coefficient inequality by the power bound proves the second bound.
