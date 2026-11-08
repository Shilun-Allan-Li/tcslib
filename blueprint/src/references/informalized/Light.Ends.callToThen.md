<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Calls.lean :: Light.Ends.callToThen -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# List-Based Call Followed by a Statement

**Claim.** Under the stated procedure specification, continuation executions, argument hypotheses, depth condition, and total cost bound, the call assigning its result at position $x$ in the frame of $l$, followed by $s$, executes within cost $T$ and ends in a state satisfying $Q$.

**Proof.** The list-based call theorem ( `Light.Ends.callTo`) gives an execution of the call from the frame of $l$, with cost bounded by the argument-expression costs plus $2+T'$. Its postcondition is that every resulting state admits the specified execution of $s$ within the remaining budget and with final postcondition $Q$. Apply the sequential composition theorem ( `Light.Ends.next`) to join the call and continuation executions. The assumed total cost inequality ensures the call's cost bound fits within $T$, so the composition has cost at most $T$.

**Key facts.** `Light.Ends.callTo`, `Light.Ends.next`.
