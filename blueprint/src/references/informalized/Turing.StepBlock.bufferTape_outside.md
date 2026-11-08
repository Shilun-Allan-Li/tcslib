<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepBlock.lean :: Turing.StepBlock.bufferTape_outside -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Blank Cells Outside the Stored Word

**Claim.** A buffer tape storing a finite Boolean word is blank at every integer cell that is not a nonnegative position strictly below the word's length.

**Proof.** Split according to whether the cell index $z$ is nonnegative. If it is negative, the buffer-tape definition returns blank. If it is nonnegative, the hypothesis that $z$ is not in the word's index range implies that its natural index is at least the word length. The list lookup is therefore absent, so the buffer tape again returns blank.
