<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/StartUp.lean :: Light.Compiler.straight_headStraight -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Straightness of the initialization prefix

**Claim.** Each instruction in the fixed initialization prefix is straight.

**Proof.** The prefix consists of one constant assignment followed by two subtraction instructions. Each belongs to the straight instruction cases, so every instruction in the prefix is straight.
