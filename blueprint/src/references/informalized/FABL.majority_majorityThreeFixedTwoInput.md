<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.majority_majorityThreeFixedTwoInput -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Three-Coordinate Majority with Two Fixed Inputs

**Claim.** For distinct positions $i,j$ among three coordinates and signs $a,b,s$ with $a\ne b$, majority of the vector having entries $a$ and $b$ at those positions and $s$ at the remaining position equals $s$.

**Proof.** Check the possible distinct positions $i,j$ and the sign cases. Since $a$ and $b$ are opposite signs, their contributions to the coordinate sum cancel, leaving exactly the remaining sign $s$. Its threshold sign is therefore $s$, proving the assertion.
