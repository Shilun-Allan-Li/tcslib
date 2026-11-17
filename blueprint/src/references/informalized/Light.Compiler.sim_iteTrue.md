<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/Simulation.lean :: Light.Compiler.sim_iteTrue -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# True-Branch Conditional Simulation

**Claim.** If the condition is safe and holds in the initial state, and the true branch is simulated with cost $k$, then the conditional is simulated to the same final state with cost $\operatorname{cost}(c)+1+k$.

**Proof.** Fix a valid starting machine configuration for the conditional. Its width bound gives the required bounds for the condition and both branches, and its code is laid out as condition test, true branch, an unconditional jump over the false branch, then false-branch code. Simulating the condition with its truth value true takes at most $\operatorname{cost}(c)$ machine steps and changes only scratch cells. The memory relation is therefore preserved for the resulting configuration, which supplies a valid starting configuration for the true branch. Apply the assumed simulation of that branch. Since the branch leaves the distinguished negative-one cell intact, the instruction after it jumps over the false branch in one step. Concatenating these runs reaches the end of the conditional code; the code-size identities reconcile the final program counter, and the total machine-step bound is at most the prescribed $\mathrm{stepsPerStep}(S.disp)\bigl(\operatorname{cost}(c)+1+k\bigr)$. The final memory relation comes from the true-branch simulation. For the write-set condition, enlarge the condition's scratch-cell agreement to the statement's writable cells and compose it with the branch's agreement.

**Key facts.** `Light.Compiler.Stmt.width_ite_le_iff`, `Light.Compiler.codeAt_ite`, `Light.Compiler.Start.test`, `Light.Compiler.Decides.of_holds`, `Light.Compiler.Rel.same`, `Light.Compiler.Start.sub`, `WordRAM.Steps.trans`, `Light.Compiler.Sizes.inRange_neg_one`, `Light.Compiler.steps_jump`, `Light.Compiler.add_le_stepsPerStep_mul`, `Light.Compiler.scratch_subset_writable`, `WordRAM.AgreeOutside.mono`, `WordRAM.AgreeOutside.trans`, `WordRAM.Steps.cast_count`, `WordRAM.Steps.cast_pos`.
