<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/CountSort.lean :: Light.CsSummed.start -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Summed-Counter Invariant

**Claim.** If the counter at offset zero contains zero and each cell at offset $t+1$ contains the number of keys equal to $t$, then the summed-counter conditions hold at stage zero.

**Proof.** For the start condition, the only offset $t$ with $t\le 0$ is $t=0$. The number of keys below zero is zero, since no natural key is below zero; hence the cell at offset zero has the required value. The size condition at stage zero asks for the given equality-count value at each offset $t+1$ with $t<N_b$, because $0\le t$ holds automatically. This is exactly the assumed counter-cell condition.
