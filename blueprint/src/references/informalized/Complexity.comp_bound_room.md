<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.comp_bound_room -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Room in the Computational Bound

**Claim.** For $B=8(2C+3)(n+1)^{e+1}$, both $n+1\le B$ and $2(2C+3)(n+1)^{e+1}\le B$ hold.

**Proof.** Since $e+1\ge 1$ and $n+1\ge 1$, monotonicity of natural-number powers gives $(n+1)^1\le(n+1)^{e+1}$, so $n+1\le(n+1)^{e+1}$. The coefficient $8(2C+3)$ is at least $1$, yielding the first bound. For the second, write $B=4\cdot 2(2C+3)(n+1)^{e+1}$; the claimed inequality follows because $4\ge1$.
