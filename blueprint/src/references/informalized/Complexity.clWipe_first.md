<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clWipe_first -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First Completion of a Scratch Reset

**Claim.** There is a positive time at most $2|w|+2$ at which the reset machine first reaches its completed control, with the stream unchanged, the target erased, and the target head at zero.

**Proof.** The reset-run calculation shows that after exactly $2|w|+2$ steps, the machine reaches the specified completed configuration (`Complexity.clWipe_run`). That configuration has control state $2$, while the starting configuration has control state $0$, so it did not start in the completed control. Moreover, every configuration in control state $2$ is stationary (`Complexity.clWipe_idle`). The first-entry principle for a stationary target state therefore supplies a positive first time no greater than the displayed run bound, with no earlier run configuration in control state $2$ and with the same completed endpoint (`Complexity.clFirst`).

**Key facts.** `Complexity.clFirst`, `Complexity.clWipe_idle`, `Complexity.clWipe_run`.
