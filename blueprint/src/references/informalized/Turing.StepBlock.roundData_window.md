<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepBlock.lean :: Turing.StepBlock.roundData_window -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Round Configuration Head Window

**Claim.** The constructed configuration's input head and each original work-tape head are at either their positions in the original configuration or their positions after the action is applied.

**Proof.** Split on the Boolean choice. If it is false, the construction uses the original configuration $c$, so the input-head and original work-head positions agree with their starting positions. If it is true, it uses $a$ applied to $c$, so those positions agree with their finishing positions. The added auxiliary tapes do not affect these coordinates: the original tapes occupy the first $k$ indices, and the input position is copied directly. Hence each required position is one of the two stated alternatives.
