<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/Simulation.lean :: Light.Compiler.sim_whileFalse -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# False While-Loop Simulation

**Claim.** If condition $c$ is safe and does not hold in $\sigma$, then the loop that executes $s$ while $c$ holds is simulated from $\sigma$ to itself with cost $\operatorname{cost}(c)+1$.

**Proof.** Fix a valid starting configuration for the loop. The loop's width bound supplies the condition's width bound, and its code begins with the condition test. Since the condition is safe and false, the test simulation reaches the loop's exit position in at most $\operatorname{cost}(c)$ machine steps, changing only scratch cells. Thus the frame relation still represents the same state, and scratch-cell agreement implies agreement outside the writable region. The test's exit position is the position after the loop code, because the loop body and back-jump are skipped. The resulting run therefore has the required endpoint, and its step bound is at most the bound for cost $\operatorname{cost}(c)+1$.

**Key facts.** `Light.Stmt.width_while_le_iff`, `Light.Compiler.codeAt_while`, `Light.Compiler.Start.test`, `Light.Compiler.Decides.of_fails`, `Light.Compiler.Rel.same`, `Light.Compiler.le_stepsPerStep_mul`, `Light.Compiler.scratch_subset_writable`, `WordRAM.AgreeOutside.mono`, `WordRAM.Steps.cast_pos`.
