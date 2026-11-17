<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.CoordinateDecisionTree.exists_finish_depth_ge_sub_of_depth_queryCoordinates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth of a Queried-Coordinate Tree

**Claim.** If the tree formed by querying the coordinates in $C$ from seed $s$ has depth at least $k$, and $|C|<k$, then some input $x$ has a finishing tree of depth at least $k-|C|$.

**Proof.** Induct on the list $C$, allowing both the seed and $k$ to vary. If the list is empty, the queried tree is the finishing tree at the seed, so that tree itself has depth at least $k$. Otherwise write $C=j::C'$. The depth bound says that the maximum of the depths of the two recursively queried trees is at least $k-1$. Hence one branch, for a bit value zero or one at $j$, has depth at least $k-1$. The length hypothesis gives $|C'|<k-1$, so the induction hypothesis applied to that branch yields an input $x$ whose finishing tree has depth at least $(k-1)-|C'|$. Since $|C|=|C'|+1$, this is exactly $k-|C|$.
