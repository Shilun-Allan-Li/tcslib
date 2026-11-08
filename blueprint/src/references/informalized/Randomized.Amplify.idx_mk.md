<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplify.lean :: Randomized.Amplify.idx_mk -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second Coordinate of a Product Index

**Claim.** For indices $j<r+1$ and $i<k$, the second coordinate of the product index corresponding to $(j,i)$ is $i$.

**Proof.** The product-index equivalence sends the pair $(j,i)$ to its corresponding index, and its inverse recovers the original pair. Taking the second coordinate of that recovered pair therefore gives $i$.
