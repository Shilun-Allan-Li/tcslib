<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyConfigStep.lean :: Complexity.CfgTableau.optOf_isSome_getD -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reconstruction of an Optional Boolean

**Claim.** For every optional Boolean $o$, using its presence flag and its value with default false reconstructs exactly $o$.

**Proof.** If $o$ is `none`, its presence flag is false, so the construction returns `none`. If $o$ is `some b`, its presence flag is true and its defaulted value is $b$, so the construction returns `some b$. These cases give the claimed equality.
