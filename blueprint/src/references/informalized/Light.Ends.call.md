<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Logic.lean :: Light.Ends.call -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cost Bound for a Procedure Call

**Claim.** If procedure $p$ has body $body$, and that body executes at depth $d+1$ from the argument frame and initial memory with cost at most $T'$ and a final state satisfying the call's postcondition, then the call executes at depth $d$ with cost at most $T$, provided its arguments are safe, the body is listed at $p$, the depth limit permits the call, and the argument costs plus $2+T'$ are at most $T$.

**Proof.** Unpack the body execution hypothesis to obtain a final state, its cost $k$, the execution of $body$, the bound $k\leq T'$, and the final-state postcondition. The call execution rule (as used directly in the proof) combines this execution with argument safety, the fact that $body$ is the procedure at index $p$, and $d<\mathrm{lim.depth}$. It yields a call execution whose cost is the sum of the argument-expression costs, $2$, and $k$. Because $k\leq T'$ and the assumed total bound is at most $T$, this call cost is at most $T$; its final-state postcondition is exactly the one supplied by the body hypothesis.
