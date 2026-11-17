<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.recursiveMajorityThreeBlockCoordinates_disjoint -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Disjoint Three-Block Coordinates

**Claim.** For distinct $i,j\in\{0,1,2\}$, the coordinate blocks associated with $i$ and $j$ in the recursive three-way construction at depth $d+1$ are disjoint.

**Proof.** Suppose a coordinate $k$ belonged to both blocks. Membership in each block means that there are coordinates $a,b\in\mathrm{Fin}(3^d)$ such that $k$ is the embedding of $(i,a)$ and also the embedding of $(j,b)$. Removing the common finite-index cast shows that the two product-equivalence images are equal. Since the product equivalence is injective, their first components agree, so $i=j$, contradicting the hypothesis that they are distinct. Thus no coordinate lies in both blocks, proving disjointness.
