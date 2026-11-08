<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/DirectedWalk.lean :: Randomized.avgOut_chainDigraph -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Average over chain out-neighbours

**Claim.** For $i<n$, the average of $f$ over the out-neighbours of $i$ in the chain digraph on $\mathrm{Fin}(n+1)$ is $(f(0)+f(i+1))/2$.

**Proof.** The out-neighbours of $i$ are exactly $0$ and $i+1$, by the adjacency definition. The hypothesis $i<n$ ensures that $i+1$ is a vertex, and also that these two vertices are distinct. Thus the out-neighbour set is nonempty, has cardinality two, and its sum of $f$-values is $f(0)+f(i+1)$. Substituting this set, sum, and cardinality into the definition of the out-neighbour average gives the claimed formula.
