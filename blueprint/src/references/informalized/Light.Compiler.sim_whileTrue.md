<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/Simulation.lean :: Light.Compiler.sim_whileTrue -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# True While-Loop Simulation

**Claim.** If $c$ is safe and true in $\sigma$, the body is simulated from $\sigma$ to $\sigma_1$ with cost $k_1$, and the loop from $\sigma_1$ to $\sigma_2$ is simulated with cost $k_2$, then the loop is simulated from $\sigma$ to $\sigma_2$ with cost $\operatorname{cost}(c)+1+k_1+k_2$.

**Proof.** Fix a valid starting configuration. The width bound gives bounds for the condition and body, while the loop code consists of the test, body, and a jump back to the test. Because the condition holds, its safe test reaches the body in at most $\operatorname{cost}(c)$ steps and changes only scratch cells. The resulting relation starts the body's simulation. After the body, its execution preserves boundedness of the state; its resulting relation therefore starts the recursive loop simulation at the original loop position. The back-jump is one step because the negative-one cell has its represented value and is in range. Concatenate the test, body, jump, and recursive-loop runs. Their endpoints align to give the end of the recursive loop run, and the run count is adjusted to the claimed sum. The test and body bounds combine into the machine-step bound for one loop iteration, which adds to the recursive bound. Finally, the recursive simulation gives the final relation, and transitivity combines the three agreement guarantees after extending scratch-cell agreement to writable cells.

**Key facts.** `Light.Stmt.width_while_le_iff`, `Light.Compiler.codeAt_while`, `Light.Compiler.Start.test`, `Light.Compiler.Decides.of_holds`, `Light.Compiler.Rel.same`, `Light.Compiler.Start.sub`, `WordRAM.Steps.trans`, `Light.Compiler.Sizes.inRange_neg_one`, `Light.Compiler.steps_jump`, `Light.Exec.bounded`, `Light.Compiler.add_le_stepsPerStep_mul`, `Light.Compiler.scratch_subset_writable`, `WordRAM.AgreeOutside.mono`, `WordRAM.AgreeOutside.trans`, `WordRAM.Steps.cast_count`.
