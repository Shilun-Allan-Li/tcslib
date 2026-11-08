<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyConfigStep.lean :: Complexity.tableauAccepted_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance Recurrence

**Claim.** The machine has emitted $1$ at some time strictly before $t+1$ exactly when it has emitted $1$ at some time strictly before $t$, or its transition at time $t$ emits $1$.

**Proof.** The times strictly below $t+1$ split into those strictly below $t$ and the single time $t$. Consequently, a witness time for an emission of $1$ below $t+1$ either witnesses the first alternative or equals $t$, witnessing the second. Conversely, a witness below $t$ is also below $t+1$, and an emission at time $t$ is below $t+1$. These two inclusions establish the Boolean recurrence.
