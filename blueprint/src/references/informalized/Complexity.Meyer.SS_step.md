<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerTableau.lean :: Complexity.Meyer.SS_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# State and Output Summary After One Step

**Claim.** After one machine step, the state and output summary is obtained by applying the summary update rule to the current summary and the symbols read in the current configuration.

**Proof.** Split according to whether the configuration is halted. If halted, the step leaves it unchanged, and the summary update rule also leaves the summary unchanged. If active in state $q$, the step applies the transition selected by the current reads (`Complexity.Meyer.step_eq`). The resulting state is the transition's successor state, while the output list is the old output followed by the transition's optional output. The summary of this concatenated output is obtained by pushing that optional output onto the summary of the old output (`Complexity.TimeHierarchy.OutReg.ofList_push`). Therefore the resulting state and output summary is exactly the value prescribed by the summary update rule.

**Key facts.** `Complexity.Meyer.step_eq`, `Complexity.TimeHierarchy.OutReg.ofList_push`.
