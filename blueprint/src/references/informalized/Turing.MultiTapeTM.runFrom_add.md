<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Deterministic.lean :: Turing.MultiTapeTM.runFrom_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Splitting a Run

**Claim.** Running for $a+b$ steps from a configuration gives the same result as running for $b$ steps from the configuration reached after $a$ steps.

**Proof.** A run for $n$ steps is the $n$-fold iterate of the one-step transition function. The iterate law says that the iterate of order $a+b$ is the composition of the iterates of orders $a$ and $b$; reversing the order of the summands if needed gives first $a$ steps, then $b$ steps. Applying this composition to the starting configuration proves the equality.
