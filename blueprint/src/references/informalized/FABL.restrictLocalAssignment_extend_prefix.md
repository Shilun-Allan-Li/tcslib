<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPThreeQuery.lean :: FABL.restrictLocalAssignment_extend_prefix -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restriction of an Extended Assignment

**Claim.** If $a\leq K$, restricting the extension of an original sign assignment by an auxiliary assignment on $K$ coordinates to the first $r+a$ coordinates gives the extension by the first $a$ auxiliary signs.

**Proof.** Compare the two assignments coordinatewise, using the decomposition into original and auxiliary coordinates. On an original coordinate, both sides return the original assignment. On an auxiliary coordinate among the first $a$, restriction selects the corresponding coordinate of the length-$K$ auxiliary assignment, which is exactly the value specified by its first-$a$ restriction. Therefore the two assignments agree everywhere.
