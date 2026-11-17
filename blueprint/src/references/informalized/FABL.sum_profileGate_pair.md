<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/ThresholdCircuits.lean :: FABL.sum_profileGate_pair -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sum of Profile Gate Pairs

**Claim.** For each coordinate, add the real-valued outputs of its profile main gate and profile correction gate at $x$. Summing these pairs over all coordinates gives the sign value $a(c)-a(0)$, where $c$ is the number of coordinates in $S$ at which $x$ equals $1$.

**Proof.** The contribution from the pair at coordinate $i$ is the difference between the sign values at $i+1$ and $i$ when $i<c$, and is zero otherwise (`FABL.profileGate_pair_value`). Consequently the sum over the $n$ coordinates reduces to the sum of these successive differences for $i=0,\ldots,c-1$: the count satisfies $c\le |S|\le n$, so no terms are omitted. This finite telescoping sum is $a(c)-a(0)$.

**Key facts.** `FABL.profileGate_pair_value`, `FABL.positiveCoordinateCountOn_le`.
