<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.MachineFormat.summaryClock_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Summary clock at time zero

**Claim.** For every finite-state multi-tape Turing machine over bits and every finite bit string, the summary clock at time zero, started in the initial configuration with no output summary, equals false.

**Proof.** At time zero the clock returns the conjunction of the configuration’s halting test and the test that the supplied summary is `some true`. The initial configuration has a state, so it is not halted; moreover, the supplied summary is none. Hence the conjunction is false.
