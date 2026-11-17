<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerMachineParse.lean :: Complexity.Meyer.two_02_1 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unmodified middle coordinate

**Claim.** After setting coordinate $0$ to $a$ and then coordinate $2$ to $a'$, the resulting function has the default value $(\mathrm{none},0)$ at coordinate $1$.

**Proof.** Coordinate $1$ is distinct from both updated coordinates, so both updates leave its value unchanged. The initial function is constant with value $(\mathrm{none},0)$, giving the stated value.
