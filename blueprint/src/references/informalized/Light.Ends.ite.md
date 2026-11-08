<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Logic.lean :: Light.Ends.ite -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Execution of a Conditional

**Claim.** If the condition is safe and each branch executes within cost $T'$ to a state satisfying $Q$ whenever that branch is selected, then the conditional executes within cost $T$ to a state satisfying $Q$, provided the stated cost inequality holds.

**Proof.** Split according to whether $c$ holds in the initial state. If it holds, the first branch hypothesis supplies an execution of $s_1$ with some actual cost at most $T'$ and final state satisfying $Q$. The conditional execution rule adds the cost of evaluating the condition and its branch overhead, namely $\mathrm{cost}(c)+1$; the assumed inequality bounds the total by $T$. If $c$ does not hold, use the second branch hypothesis and the corresponding conditional execution rule, with the same cost estimate. In either case the condition is safe, so the resulting execution is valid and has the required postcondition.
