<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/ThresholdCircuits.lean :: FABL.positiveCoordinateCountOn_add_negativeCoordinateCountOn -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive and Negative Coordinate Counts

**Claim.** For any finite set $S$ of coordinates and any sign vector $x$, the number of coordinates in $S$ where $x$ is $+1$ plus the number where it is $-1$ equals $|S|$.

**Proof.** Partition $S$ into coordinates where $x_i=1$ and those where $x_i\ne1$. The cardinalities of these two parts sum to $|S|$ by the finite-set filter partition identity. Every coordinate value is a sign, hence is either $+1$ or $-1$; therefore the second part is exactly the set of coordinates where $x_i=-1$. Its cardinality is the negative-coordinate count, proving the claim.
