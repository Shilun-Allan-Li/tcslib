<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkHitting.lean :: Randomized.RegularMultigraph.avg_mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of neighbor averages

**Claim.** If $f(v)\le g(v)$ at every vertex, then the neighbor average of $f$ is at most the neighbor average of $g$ at every vertex.

**Proof.** Fix a vertex $s$. For each neighbor slot, the pointwise hypothesis gives $f(G.\mathrm{nbr}(s,i))\le g(G.\mathrm{nbr}(s,i))$. Summing these inequalities over all slots preserves the inequality. Dividing by the positive degree $D$ also preserves it, so the average of $f$ at $s$ is at most the average of $g$ there.
