<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumCont_return_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Simulation Through Halt Redirection

**Claim.** If the host machine's transitions from embedded states reproduce the simulated machine's actions, redirecting halting successors to a return state, then for a run that is live before time $t$, the host run agrees at time $t$ with the simulated run under the state correspondence.

**Proof.** Induct on the number of steps. At time zero the configurations agree by the definition of the state correspondence. For the successor step, the run-succession law expresses each run as one step after its time-$t$ configuration (`Turing.MultiTapeTM.runFrom_succ_eq_step'`). The induction hypothesis identifies those time-$t$ configurations, and the liveness assumption guarantees that the simulated machine's state there is present. Its current state is therefore some $q$, rather than the halted case. By the transition hypothesis, the host transition from the embedded state has the same input movement, tape actions, and output as the simulated transition, with its successor embedded if present and replaced by the return state if absent. Applying these actions gives precisely the corresponding next configuration, completing the induction.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
