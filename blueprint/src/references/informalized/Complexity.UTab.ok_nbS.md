<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitterInstr.lean :: Complexity.UTab.ok_nbS -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Validity of a conditional previous-cell source

**Claim.** If $ok$ being true implies $1\leq\rho(r_Q)+d$, then the source that is the $j$th previous-cell source with offset $d$ when $ok$ is true and constant false otherwise is valid for $\rho$.

**Proof.** Split on whether $ok$ is true. In the true case the source is a previous-cell source with offset $d$, and its validity condition is precisely $1\leq\rho(r_Q)+d$, supplied by the hypothesis. In the false case the source is constant false, which is valid by definition.
