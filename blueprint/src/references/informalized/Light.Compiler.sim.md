<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/Simulation.lean :: Light.Compiler.sim -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Simulation of Executions

**Claim.** Every execution of a statement in the light language is simulated by its compiled code, with the stated step bound, final state relation, and agreement outside writable addresses.

**Proof.** Proceed by induction on the derivation of the light-language execution. For a skip, assignment, or memory store, the corresponding simulation result for that basic statement gives the compiled run, step bound, represented final state, and writable-region agreement (`sim_skip`, `sim_set`, `sim_store`). For sequential composition, apply the induction hypotheses to the two executions in order and concatenate their machine runs; the step counts add (`sim_seq`). For a conditional whose condition holds, use the true-branch result (`sim_iteTrue`); when it fails, use the false-branch result (`sim_iteFalse`). In either case the condition test selects the corresponding compiled branch before that branch’s simulation is used. A false loop condition yields the loop simulation directly (`sim_whileFalse`). For a true loop condition, apply the induction hypothesis first to the body and then to the remaining loop execution, and combine them with the loop result (`sim_whileTrue`). Finally, for a procedure call, the induction hypothesis for the called body at the next depth is combined with the call simulation result (`sim_call`). These cases exhaust the execution rules and establish the simulation statement for each derivation.

**Key facts.** `Light.Compiler.sim_skip`, `Light.Compiler.sim_set`, `Light.Compiler.sim_store`, `Light.Compiler.sim_seq`, `Light.Compiler.sim_iteTrue`, `Light.Compiler.sim_iteFalse`, `Light.Compiler.sim_whileFalse`, `Light.Compiler.sim_whileTrue`, `Light.Compiler.sim_call`.
