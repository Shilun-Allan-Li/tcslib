<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitterInstr.lean :: Complexity.UTab.ok_chS -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Validity of a conditional source

**Claim.** If $ok$ is true only under the assumption that $1\leq\rho(r_I)$, then the source that is the $j$th current-cell source when $ok$ is true and constant false otherwise is valid for $\rho$.

**Proof.** Split on whether $ok$ is true. In the true case the source is the $j$th current-cell source, whose validity requires exactly $1\leq\rho(r_I)$; the hypothesis supplies it. In the false case the source is constant false, which is valid by definition.
