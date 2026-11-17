<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Deterministic.lean :: Turing.MultiTapeTM.step_output -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output Appended in One Step

**Claim.** After one step, the configuration's output is its current output followed by the symbol emitted in that step, if any; if no symbol is emitted, the output is unchanged.

**Proof.** Split according to whether the configuration is halted. In the halted case, a step leaves the configuration unchanged and no output symbol is emitted, so the claimed formula holds. In the nonhalted case, the machine applies its transition action. By the definition of applying an action, the new output is the old output followed by the list associated to the action's optional output symbol. This is exactly the stated formula, including the empty-list case when no symbol is emitted.
