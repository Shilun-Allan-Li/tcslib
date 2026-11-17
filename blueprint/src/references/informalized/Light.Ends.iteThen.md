<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Rules.lean :: Light.Ends.iteThen -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Conditional Followed by a Continuation

**Claim.** If the selected branch followed by the continuation executes within the budget remaining after evaluating the condition, then the conditional followed by that continuation executes within total budget $T$ and ends in a state satisfying $Q$.

**Proof.** Split according to whether $c$ holds in the initial state. In the true case, the assumed bounded execution of $s_1$ followed by $s$ supplies an execution derivation for that sequence; its sequential form consists of an execution of $s_1$ followed by an execution of $s$. Replace the first execution by the true-branch conditional execution, which evaluates the safe condition and then runs $s_1$. Compose this conditional execution with the unchanged execution of $s$. In the false case, use the assumed execution of $s_2$ followed by $s$ and replace its first component with the false-branch conditional execution. In either case, the final state and $Q$ are preserved. The branch's cost bound is $T-(\mathrm{cost}(c)+1)$, so adding the condition-evaluation cost $\mathrm{cost}(c)+1$ gives a total at most $T$.
