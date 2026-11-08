<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplify.lean :: Randomized.Amplify.blk_mk -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Block Coordinate of a Product Index

**Claim.** For $j<r+1$ and $i<k$, the block coordinate of the standard product encoding of $(j,i)$ is $j$.

**Proof.** The standard product encoding is inverted by the product equivalence: decoding the index of $(j,i)$ returns the pair $(j,i)$. Its first coordinate is therefore $j$, which is exactly the block coordinate by definition.
