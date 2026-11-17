<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Logic.lean :: Light.Ends.seq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sequential Composition of Bounded Executions

**Claim.** If $s_1$ executes within $T_1$ to a state from which $s_2$ executes within $T_2$ ending in $Q$, and $T_1+T_2\le T$, then $s_1;s_2$ executes within $T$ ending in $Q$.

**Proof.** Unpack the bounded-execution witnesses. The first gives an intermediate state and cost $c_1\le T_1$; the second gives a final state satisfying $Q$ and cost $c_2\le T_2$. Compose the two executions using the sequential execution rule. Its cost is $c_1+c_2$, which is at most $T_1+T_2$ and hence at most $T$. The final state still satisfies $Q$.
