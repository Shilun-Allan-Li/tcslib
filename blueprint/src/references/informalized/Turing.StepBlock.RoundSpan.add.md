<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepBlock.lean :: Turing.StepBlock.RoundSpan.add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Concatenating Round Spans

**Claim.** If a round-machine run from $d$ to $e$ is a valid round span of length $T$, and a run from $e$ to $f$ is a valid round span of length $U$, then the run from $d$ to $f$ is a valid round span of length $T+U$.

**Proof.** The run composition law says that running for $T+U$ steps is the same as first running for $T$ steps and then for $U$ steps (`Turing.MultiTapeTM.runFrom_add`). Since the first run ends at $e$ and the second at $f$, the composite run ends at $f$. Now take any time $u<T+U$. If $u<T$, the left span supplies an intermediate state and the required window condition. Otherwise write $u=T+(u-T)$. The configuration at time $u$ is then the configuration reached from $e$ after $u-T$ steps, by the composition law and the left run's endpoint. Since $u-T<U$, the right span supplies the required state and window condition there. Thus every time strictly before $T+U$ satisfies the span conditions.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`.
