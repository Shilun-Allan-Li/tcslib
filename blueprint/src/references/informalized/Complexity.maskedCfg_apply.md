<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSchedule.lean :: Complexity.maskedCfg_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Masking Commutes with Actions

**Claim.** Applying an action and then replacing the input by the constant word of the same length gives the same configuration as masking the input first and then applying the action.

**Proof.** Compare the resulting configurations component by component. The state is the action’s successor state in either order. For the input-head position, both computations start from the same numerical head position, and the masked input has the same length as the original input; hence the boundary-clamped head movement is identical. The work tapes and their head positions are unchanged by masking, so the action makes the same writes and movements in either order. The output is likewise the original output followed by the action’s emitted symbols in both cases. Therefore the configurations agree.
