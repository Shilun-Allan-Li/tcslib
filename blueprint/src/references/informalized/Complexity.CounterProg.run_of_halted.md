<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CounterProg.lean :: Complexity.CounterProg.run_of_halted -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stationarity of Halted States

**Claim.** If a state is halted, running the program from it for any number of steps leaves the state unchanged.

**Proof.** Induct on the number of steps. At zero steps the run is the original state. For the successor case, decompose the run into one step followed by the remaining run, using the run decomposition law (`Complexity.CounterProg.run_succ`). Since the state is halted, its label is `none`, and a single step leaves every component unchanged. The induction hypothesis then shows that the remaining run also leaves the state unchanged.

**Key facts.** `Complexity.CounterProg.run_succ`.
