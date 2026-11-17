<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerMachineParse.lean :: Complexity.Meyer.two_12_0 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unmodified first coordinate

**Claim.** After setting coordinate $1$ to $a$ and then coordinate $2$ to $a'$, the resulting function has the default value $(\mathrm{none},0)$ at coordinate $0$.

**Proof.** Coordinate $0$ is distinct from both updated coordinates, so neither update changes its value. Its value remains the initial constant value $(\mathrm{none},0)$.
