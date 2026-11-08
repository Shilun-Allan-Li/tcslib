<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Seam.lean :: Turing.seamCompTM_visitedByTapeHead_ofCfg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Visited Cells for General Configurations

**Claim.** For any work-tape index, the cells visited in the composed run from the left-embedded initial configuration lie in the union of the cells visited by the first machine through its exit time and by the second machine from the entry-state version of the exit configuration.

**Proof.** Apply the general visited-cell inclusion result (`seamComp_visited_general`) to the first machine’s run from $c_0$ to $c_1$, the fact that $c_1$ is in the exit state, and the hypothesis that the exit state is avoided at every earlier time. The result gives exactly the asserted inclusion, for every duration of the second phase.

**Key facts.** `Turing.seamComp_visited_general`.
