<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.dropValues_update -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating a Drop Value

**Claim.** Updating coordinate $r$ of $(p,n,z,s,u,f,q,t,a)$ to $b$ yields the vector whose coordinate $j$ is $b$ if $j=r$ and is its original value otherwise.

**Proof.** Equality of the two vectors follows by checking their coordinates. At coordinate $r$, the update assigns $b$. At any other coordinate, the update leaves the original value unchanged; the displayed conditional expressions specify precisely these two cases for each of the nine coordinates.
