<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Regions.lean :: Light.SameOn.mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of memory agreement

**Claim.** Agreement on the indices satisfying $K$ implies agreement on the indices satisfying $K'$, provided every index satisfying $K'$ also satisfies $K$.

**Proof.** Take any index satisfying $K'$. By the inclusion assumption it satisfies $K$, so the given agreement on $K$ yields equality of the two memory values at that index. This proves agreement throughout $K'$.
