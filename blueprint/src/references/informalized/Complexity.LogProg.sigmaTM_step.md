<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Bank.lean :: Complexity.LogProg.sigmaTM_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Step Tagged Machine Simulation

**Claim.** For every input, machine index, and configuration, one step of the combined machine from the configuration tagged by that index equals the result of stepping the indexed machine and tagging its result.

**Proof.** Split according to whether the original configuration is halted. If its state is absent, both machines remain at their configurations, and tagging preserves every component. If its state is a state $q$, the tagged configuration has state tagged by the same index and $q$. By the definition of the combined machine, its transition in this tagged state uses exactly the transition of the indexed machine at $q$; it retains that machine's tape actions, input-head movement, and output, while tagging any successor state with the same index. Applying this action therefore gives precisely the tagged configuration obtained by stepping the indexed machine.
