<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/CountSort.lean :: Light.CsCounted.start -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial counter state

**Claim.** If all $A.nb+1$ counter cells are zero, then the initial counted-state invariant holds for zero processed indices.

**Proof.** The first counter cell is zero by the zeroed-cell hypothesis at offset $0$. For any key $t<A.nb$, the cell at offset $t+1$ is also zero, since $t+1<A.nb+1$. The number of indices below zero having key $t$ is zero, so this cell has exactly the required count.
