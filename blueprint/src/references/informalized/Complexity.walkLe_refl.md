<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathWalk.lean :: Complexity.walkLe_refl -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reflexive Bounded Walks

**Claim.** For every bound $j$ and vertex $c$, there is a bounded walk from $c$ to itself.

**Proof.** If $j=0$, the defining condition for a walk is equality, which holds from $c$ to itself. If $j$ is positive, the equality alternative in the definition gives the required walk immediately.
