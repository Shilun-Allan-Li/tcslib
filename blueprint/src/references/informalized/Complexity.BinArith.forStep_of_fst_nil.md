<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Loops.lean :: Complexity.BinArith.forStep_of_fst_nil -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# For-Step with Empty First Projection

**Claim.** If the total first projection of a bit string $S$ is empty, then one application of the for-step transformation leaves $S$ unchanged.

**Proof.** The for-step tests whether the total first projection is empty. Under the hypothesis it is empty, so the transformation takes its unchanged-state branch and returns $S$.
