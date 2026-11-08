<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Wrappers.lean :: Turing.FinTM.redirect_loop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# The redirect loop is fixed

**Claim.** Any configuration in the loop state of the redirected machine is unchanged after any number of steps.

**Proof.** Induct on the number $t$ of steps. At zero steps the run is the starting configuration. For the successor case, first run for $t$ steps; by induction this returns the same configuration. One further step from a loop-state configuration applies the loop transition, which leaves the input head, work tapes, work-head positions, output, and loop state unchanged. Hence the run after $t+1$ steps is again the original configuration.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
