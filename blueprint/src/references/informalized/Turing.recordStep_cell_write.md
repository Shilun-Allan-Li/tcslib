<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean :: Turing.recordStep_cell_write -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recorded Work-Cell Update

**Claim.** Applying the action's write instruction to a recorded cell gives the post-action content at that position and leaves its head mark unchanged.

**Proof.** Separate whether $z$ is the head position. If it is, the mark is true and the action's optional write instruction updates exactly that cell; if no write is prescribed, its content remains unchanged. If $z$ is not the head position, the mark is false, so the recorded-cell transformation preserves its content. Applying the action also leaves every non-head cell unchanged. In both cases the mark remains the same test of whether the original head position equals $z$, as required.
