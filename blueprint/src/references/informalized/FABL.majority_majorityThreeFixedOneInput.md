<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.majority_majorityThreeFixedOneInput -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Three-Coordinate Majority with One Fixed Input

**Claim.** For any position $i$ among three coordinates and signs $a,s$, majority of the vector with entry $a$ at $i$ and entries $s$ at the other positions equals $s$.

**Proof.** Check the three possible positions of $i$, and then the four possible pairs of signs $(a,s)\in\{-1,1\}^2$. In each case the coordinate sum has the sign of $s$: if $s=1$, the sum is either $1$ or $3$; if $s=-1$, it is either $-1$ or $-3$. The threshold sign therefore equals $s$, as required.
