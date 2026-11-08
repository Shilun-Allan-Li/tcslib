<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPConstructions.lean :: FABL.subsetIndicatorSign_coordinateTrueIndexSet -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinate truth table representation

**Claim.** For each coordinate, the sign vector that is negative exactly on indices encoding strings with that coordinate true is the coordinate truth table, with true represented by $-1$ and false by $1$.

**Proof.** Evaluate both sign vectors at an arbitrary index. If the decoded coordinate bit is true, the index belongs to the filtered set of true-coordinate indices, so the subset indicator sign is $-1$; the truth table also gives $-1$ for true. If the bit is false, it does not belong to that set, so the subset indicator sign is $1$, matching the truth table's value for false. The two vectors therefore agree at every index.
