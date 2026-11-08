<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/RunsStayInLimits.lean :: Light.Exec.mem_outside -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Memory Outside the Address Range

**Claim.** If a statement executes under limits, program $P$, and depth $d$, from state $\sigma$ to state $\sigma'$ with cost $c$, then every address $a$ at least the space limit has unchanged memory: $\sigma'.\operatorname{mem}(a)=\sigma.\operatorname{mem}(a)$.

**Proof.** Induct on the execution derivation. A skip or location assignment leaves memory unchanged. For a store, safety of its address gives an address strictly below the space limit; hence it differs from $a$, and updating memory at that address leaves the value at $a$ unchanged. In a sequential execution, apply the induction hypothesis first to the second execution step and then to the first. A conditional execution inherits the result from its selected branch. A loop that exits immediately preserves the state, while a loop that iterates inherits the result successively from its body and remaining loop execution. Finally, for a procedure call, the induction hypothesis gives equality of the callee's final and initial memory at $a$; the caller's resulting memory is that same final memory.
