<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Rules.lean :: Light.Ends.skipLast -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Removing a Final Skip

**Claim.** If $s$ followed by skip can execute from $\sigma$ within budget $T$ and end in a state satisfying $Q$, then $s$ alone can do so.

**Proof.** Unpack the execution of the sequence into an intermediate state, the cost of its first part, and the cost of its second part. By the sequential execution rule, the first part executes $s$ from $\sigma$ to that intermediate state, while the second executes skip from there. The skip rule leaves the state unchanged and has cost zero. Thus the intermediate state is also the final state satisfying $Q$, and the cost of executing $s$ is the original total cost, hence at most $T$.
