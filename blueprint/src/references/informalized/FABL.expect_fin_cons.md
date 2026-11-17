<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/TotalInfluence/MajorityOptimality.lean :: FABL.expect_fin_cons -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Average by the First Coordinate

**Claim.** The uniform average of $h$ on the $(n+1)$-dimensional sign cube is the half-sum of its averages on the slices whose first coordinate is $1$ and $-1$.

**Proof.** Regard a point of the $(n+1)$-dimensional cube as a pair consisting of its first sign and its remaining $n$ signs. This is a bijective reparametrization, so the average of $h$ equals the average over such pairs. The average over pairs is the iterated average: first average over the remaining coordinates, then over the first sign. The latter sign average is the average of the two values at $1$ and $-1$, by the sign-average formula (`expect_sign`). This gives the stated half-sum.

**Key facts.** `FABL.expect_sign`.
