<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/ThresholdCircuits.lean :: FABL.sum_signValue_on_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sign Sum on a Coordinate Subset

**Claim.** For a coordinate subset $S$, the sum of the signs over $S$ is twice the number of coordinates in $S$ equal to $1$, minus $|S|$.

**Proof.** At each coordinate, its sign is twice the indicator that it equals $1$, minus $1$, using the two cases in `signValue_eq_ite`. Summing this identity over $S$ gives twice the sum of the indicators minus the sum of $1$ over $S$. The first sum counts the coordinates of $S$ where the sign is positive, and the second is $|S|.

**Key facts.** `FABL.signValue_eq_ite`.
