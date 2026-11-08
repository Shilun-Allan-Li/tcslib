<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Clean.lean :: Complexity.LogProg.visB_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successive Visited Positions

**Claim.** The head positions visited through time $t+1$ are exactly those visited through time $t$, together with the position at time $t$.

**Proof.** By definition, the visited set through time $t+1$ is the image of the time indices in the range of length $t+1$. The range extension identity writes those indices as the earlier range together with the new index $t$. Taking the image under the head-position function turns this union into the union of the earlier visited set and the position at time $t$, which is precisely the stated insertion.
