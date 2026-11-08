<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Calls.lean :: Light.Ends.callThen -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Call Followed by a Statement

**Claim.** Under the stated procedure-execution, argument-safety, depth, and cost hypotheses, if every procedure result and memory satisfying $R$ admits a bounded execution of $s$ to $Q$, then the call assigning its result to $x$, followed by $s$, executes within total cost $T$ and ends in a state satisfying $Q$.

**Proof.** First, the call-from-a-procedure-specification theorem ( `Light.Ends.callLast`) gives an execution of the call within the argument-cost overhead plus $T'$. Its postcondition says that, for each possible resulting state, the following execution of $s$ has cost at most $T-(\sum_e\mathrm{cost}(e)+2+T')$ and ends in a state satisfying $Q$. The sequential composition theorem ( `Light.Ends.next`) composes these two executions. The call cost bound is at most $T$ by hypothesis, so the remaining budget is sufficient for the second execution; the composed execution has total cost at most $T$.

**Key facts.** `Light.Ends.callLast`, `Light.Ends.next`.
