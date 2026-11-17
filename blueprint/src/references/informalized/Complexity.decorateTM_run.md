<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSchedule.lean :: Complexity.decorateTM_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Projection of decorated runs

**Claim.** When the original machine emits no output, projecting its decorated machine's configuration after any number of steps onto the schedule gives exactly the original machine's configuration after that many steps.

**Proof.** Induct on the number of steps. At zero steps, projection of the decorated initial configuration is the original initial configuration. For the successor case, write each run at time $t+1$ as one step from its configuration at time $t$. Projection commutes with one step of the machines when the original transition emits no output (Complexity.decorateTM_step). Applying this fact and then the induction hypothesis identifies the projected successor configuration with the original machine's successor configuration. The identity expressing a run at time $t+1$ as a step after time $t$ is the run successor formula (Turing.MultiTapeTM.runFrom_succ_eq_step').

**Key facts.** `Complexity.decorateTM_step`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
