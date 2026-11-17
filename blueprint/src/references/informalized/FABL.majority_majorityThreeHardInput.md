<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.majority_majorityThreeHardInput -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Majority on a Three-Coordinate Input

**Claim.** For a sign $s$ and a coordinate $j$ among three positions, the input with value $-s$ at $j$ and value $s$ at the other two positions has majority value $s$.

**Proof.** Check the three choices of coordinate and the two possible signs. In each case the sum of the three coordinates is $2s+(-s)=s$, whose threshold sign is $s$. Hence majority returns $s$.
