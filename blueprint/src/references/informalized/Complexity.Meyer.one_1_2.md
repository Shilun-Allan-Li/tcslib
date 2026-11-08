<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerMachineParse.lean :: Complexity.Meyer.one_1_2 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Idle Value Away from the Update

**Claim.** For the function on three coordinates that equals $a$ at coordinate $1$ and is otherwise idle, its value at coordinate $2$ is $(\mathrm{none},0)$.

**Proof.** Coordinate $2$ differs from the updated coordinate $1$, so the function retains its default value there. That default is $(\mathrm{none},0)$.
