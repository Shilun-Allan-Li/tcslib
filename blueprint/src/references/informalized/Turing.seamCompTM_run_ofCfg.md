<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Seam.lean :: Turing.seamCompTM_run_ofCfg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Composition of Two Machine Runs

**Claim.** If the first machine reaches its exit state for the first time and the second machine then reaches its stated configuration from the entry state, the composed machine reaches that configuration, embedded in the right component, after the handoff and both runs.

**Proof.** Apply the general run-composition result (`seamComp_run_general`) to the given first run, its exit-state condition, the hypothesis that the exit state was not visited earlier, and the given second run. It states directly that the composed run consists of the first run, one handoff step, and the second run, with the final configuration’s state embedded in the right component.

**Key facts.** `Turing.seamComp_run_general`.
