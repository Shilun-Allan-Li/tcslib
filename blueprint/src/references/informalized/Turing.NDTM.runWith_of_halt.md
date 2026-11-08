<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Nondeterministic.lean :: Turing.NDTM.runWith_of_halt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Runs from Halted Configurations Stay Fixed

**Claim.** If a configuration has no state, then running the machine from it under any choice word leaves it unchanged.

**Proof.** Induct on the choice word. The empty word leaves the configuration unchanged. For a word beginning with a bit, unfold the run into one step followed by the run on the remaining word (`Turing.NDTM.runWith_cons`). Since the configuration has no state, the one-step halted-configuration fact says that this step leaves it unchanged (`Turing.NDTM.stepWith_of_halt`). The induction hypothesis then shows that the remaining run also leaves it unchanged.

**Key facts.** `Turing.NDTM.runWith_cons`, `Turing.NDTM.stepWith_of_halt`.
