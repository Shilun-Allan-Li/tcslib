<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Bank.lean :: Complexity.LogProg.sigmaTM_runFrom -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tagged Machine Run Simulation

**Claim.** For every input, machine index, configuration, and number of steps, running the combined machine from the tagged configuration gives the tagged result of running the indexed machine for the same number of steps.

**Proof.** The tagging map sends a machine configuration to one with the same tape contents, head positions, input-head position, and output, while tagging its state by the machine index. The one-step simulation lemma states that the combined machine's step commutes with this map (`Complexity.LogProg.sigmaTM_step`). Apply the general iteration principle that a map commuting with one-step transitions also commutes with every finite run (`Turing.MultiTapeTM.runFrom_comm_of_step`). This gives the claimed equality for $n$ steps.

**Key facts.** `Complexity.LogProg.sigmaTM_step`, `Turing.MultiTapeTM.runFrom_comm_of_step`.
