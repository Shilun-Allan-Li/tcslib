<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/ThresholdCircuits.lean :: FABL.sum_profileDecompositionGates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sum of Profile Decomposition Gates

**Claim.** For a subset $S$ of the coordinates, a sign sequence $a$, and a sign vector $x$, the sum of the outputs of the $2n$ profile decomposition gates at $x$ is $a(c)-a(0)$ in sign values, where $c$ counts the coordinates in $S$ at which $x$ equals $1$.

**Proof.** Reindex the $2n$ gates by pairs consisting of a coordinate $i$ and one of two gate positions. Summing over each pair gives the profile main gate plus its correction gate, and summing these pair contributions over $i$ is exactly the sum of profile gate pairs. The pair-sum identity (`FABL.sum_profileGate_pair`) states that this total is the sign value at the count $c$ minus the sign value at zero, proving the result.

**Key facts.** `FABL.sum_profileGate_pair`.
