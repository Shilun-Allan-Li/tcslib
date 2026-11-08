<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Zone.lean :: Turing.zoneCascadeRight_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successive Rightward Cascades

**Claim.** A rightward cascade of length $j+1$ is a paired shift at level $j+1$, followed by a length-$j$ cascade, followed by another paired shift at level $j+1$.

**Proof.** Expand the cascade as a fold over the levels $0$ through $j$. The reversed fold in its starting configuration processes the paired shifts in descending order; the forward fold then processes them in ascending order. For the list of levels through $j$, the descending sequence consists of the shift at level $j+1$ followed by the descending sequence through $j$. The ascending sequence consists of the ascending sequence through $j$ followed by the shift at level $j+1$. The fold laws for concatenated lists therefore place one such paired shift at each end of the length-$j$ cascade, giving the claimed decomposition.
