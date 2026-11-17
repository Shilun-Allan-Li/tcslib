<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CounterProg.lean :: Complexity.CounterProg.run_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successive Run Decomposition

**Claim.** The state reached after $t+1$ steps from a state $s$ is the state reached after $t$ steps from the state obtained by taking one step from $s$.

**Proof.** By definition, a run of length $t+1$ is the $(t+1)$-fold iterate of the one-step transition applied to the starting state. The successor law for function iteration says that this equals the $t$-fold iterate applied after one application of the transition. This is precisely the stated decomposition.
