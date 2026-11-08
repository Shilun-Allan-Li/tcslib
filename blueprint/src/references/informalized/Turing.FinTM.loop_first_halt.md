<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.loop_first_halt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First Halting Time

**Claim.** If a run starts in a nonhalting configuration and is halted after t steps, then it has a first halting time u with 0<u≤t, all earlier configurations are nonhalting, and its configuration at time u equals the one at time t.

**Proof.** Consider the nonempty set of times at which the run is halted; it contains t. Let u be its least element. Then the run is halted at u, and every earlier time is nonhalting by minimality. Since the starting configuration is nonhalting, u cannot be zero, and by its choice u≤t. The run-composition law decomposes the run at t into the configuration at u followed by t−u further steps (`runFrom_add`). A halted configuration stays fixed under every further run (`runFrom_of_halt`), so the configuration at t equals the one at u.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_of_halt`, `Turing.MultiTapeTM.runFrom_zero`.
