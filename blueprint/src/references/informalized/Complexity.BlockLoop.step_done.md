<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimeBlockLoop.lean :: Complexity.BlockLoop.step_done -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# The Completed Block Is Fixed

**Claim.** If $g$ is the block-loop transformation, then applying $g$ to the completed-block encoding returns that encoding.

**Proof.** Replace $g$ by the block-loop transformation. The completed-block encoding has an empty first component, so the transformation takes its first terminal branch and returns the completed-block encoding unchanged.
