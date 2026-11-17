<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPThreeQuery.lean :: FABL.restrictLocalAssignment_extend_pad -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restriction After Padding

**Claim.** If $a\leq K$, restricting the extension of an original sign assignment by the padded auxiliary assignment to the first $r+a$ coordinates gives the extension by the original auxiliary assignment.

**Proof.** Compare the two assignments at each coordinate, and use the decomposition of the first $r+a$ coordinates into original and auxiliary coordinates. At an original coordinate, both assignments return the given original sign. At an auxiliary coordinate among the first $a$, the padded assignment agrees with the original auxiliary assignment by its definition; the later padding coordinates do not occur in this restriction. Hence the assignments agree at every coordinate.
