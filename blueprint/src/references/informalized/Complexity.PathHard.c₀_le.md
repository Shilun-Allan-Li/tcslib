<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHardDecide.lean :: Complexity.PathHard.c₀_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lower Bound on the Code Width

**Claim.** For every natural number $c_0$, one has $c_0\le K(c_0+1)$, where $K$ is the specified code-width constant.

**Proof.** By definition, $K=2W+2$, so $K\ge 2$. Since $c_0\le c_0+1$ and $K\ge1$, multiplication gives $c_0\le K(c_0+1)$.
