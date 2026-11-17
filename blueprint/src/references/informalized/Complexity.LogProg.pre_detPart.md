<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARM.lean :: Complexity.LogProg.pre_detPart -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Choice-independent precondition

**Claim.** Replacing every choice instruction of a nondeterministic program by a fixed Boolean choice leaves its precondition unchanged.

**Proof.** Write the configuration as a control state, register values, and result. If the control state is halted, both preconditions are true by definition. Otherwise, inspect the instruction at the current state. If it is deterministic, the fixed-choice program retains that instruction (`Complexity.LogProg.NARM.detPart_det`), so the two preconditions agree. If it is a choice instruction, the replacement is a return instruction carrying the fixed Boolean (`Complexity.LogProg.NARM.detPart_choose`). The precondition imposes no additional condition for a return instruction, so it agrees with the nondeterministic precondition in this case as well.

**Key facts.** `Complexity.LogProg.NARM.detPart_det`, `Complexity.LogProg.NARM.detPart_choose`.
