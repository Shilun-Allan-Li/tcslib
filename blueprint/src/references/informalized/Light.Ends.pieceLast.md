<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Rules.lean :: Light.Ends.pieceLast -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Weakening an Execution Postcondition

**Claim.** An execution bounded by $T_1$ and ending in a state satisfying $R$ is also an execution bounded by $T$ and ending in a state satisfying $Q$, when $T_1\le T$ and $R$ implies $Q$.

**Proof.** Apply the monotonicity property of bounded executions (`Light.Ends.mono`) to the given execution. Its cost bound increases from $T_1$ to $T$ using $T_1\le T$, and its final-state condition changes from $R$ to $Q$ using the implication $R\Rightarrow Q$. The execution itself is unchanged.

**Key facts.** `Light.Ends.mono`.
