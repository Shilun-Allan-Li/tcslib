<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/InfluencesAndDerivatives/BooleanInfluence.lean :: FABL.isBoundaryDimensionEdge_majority_odd_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Boundary Edges of Odd-Dimensional Majority

**Claim.** In dimension $2m+1$, majority changes value across the edge in coordinate $i$ exactly when exactly $m$ of the other coordinates are positive.

**Proof.** Remove coordinate $i$, and let $c$ be the number of positive coordinates among the remaining $2m$ coordinates. Their sign sum is $2c-2m$ ( `sum_signValue_eq_two_mul_positiveCoordinateCount_sub`). The endpoint's sign sum is one more, while the flipped endpoint's is one less, by splitting each sum into coordinate $i$ and the remaining coordinates. If $c<m$, both sums are negative, so both threshold signs are $-1$. If $c=m$, the sums are $1$ and $-1$, so the threshold signs differ. If $c>m$, both sums are nonnegative, so both signs are $1$. These conclusions use the threshold rules for negative and nonnegative inputs ( `thresholdSign_of_neg`, `thresholdSign_of_nonneg`). Therefore the edge is a boundary exactly when $c=m$.

**Key facts.** `FABL.sum_signValue_eq_two_mul_positiveCoordinateCount_sub`, `FABL.thresholdSign_of_neg`, `FABL.thresholdSign_of_nonneg`.
