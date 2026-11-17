<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.recursiveMajorityThreeBlockCoordinates_union -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Three Blocks Cover the Coordinates

**Claim.** At every depth $d$, the three coordinate blocks indexed by $0$, $1$, and $2$ have union all of $\mathrm{Fin}(3^{d+1})$.

**Proof.** Take any coordinate $k\in\mathrm{Fin}(3^{d+1})$. Reindex it, using the product decomposition $3^{d+1}=3\cdot3^d$, as a pair $(i,j)$ with $i\in\mathrm{Fin}(3)$ and $j\in\mathrm{Fin}(3^d)$. The embedding of this pair into the larger coordinate set returns $k$. Since $i$ is one of $0,1,2$, the coordinate $k$ belongs to the corresponding block, and hence to the union of all three. Every coordinate is therefore in the union, which proves the equality.
