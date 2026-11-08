<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerMachineParse.lean :: Complexity.Meyer.one_2_0 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Idle Value Away from the Update

**Claim.** For the function on three coordinates that equals $a$ at coordinate $2$ and is otherwise idle, its value at coordinate $0$ is $(\mathrm{none},0)$.

**Proof.** Coordinate $0$ differs from the updated coordinate $2$, so the function retains its default value there, namely $(\mathrm{none},0)$.
