<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Rules.lean :: Light.Ends.seqAssoc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Associativity of Bounded Sequential Execution

**Claim.** If $s_1;(s_2;s_3)$ executes within $T$ from $\sigma$ to a state satisfying $Q$, then $(s_1;s_2);s_3$ does as well.

**Proof.** Unpack the bounded execution and inspect its derivation. Since its outer statement is sequential, its execution consists of an execution of $s_1$ followed by one of $s_2;s_3$. Inspecting the latter sequential execution gives an execution of $s_2$ followed by one of $s_3$. Reassociate these same three executions using the sequential execution rule to obtain an execution of $(s_1;s_2);s_3$. The resulting final state and total cost are unchanged, so the original cost bound and postcondition continue to hold.
