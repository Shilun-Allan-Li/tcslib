<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/TotalInfluence/MajorityOptimality.lean :: FABL.liftedOddMajority_isMajorityFunction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# The lifted odd majority is a majority function

**Claim.** For every $m$, the lifted odd majority on $2m+2$ coordinates agrees with the sign of the coordinate sum whenever that sum is nonzero; hence it is a majority function under the stated definition.

**Proof.** Let $y$ be the assignment consisting of the coordinates of $x$ after its first coordinate. Write $k$ and $r$ for the numbers of positive coordinates in $x$ and $y$, respectively. The sign-sum identity expresses the full sum as $2k-(2m+2)$ and the tail sum as $2r-(2m+1)$. Splitting off the first coordinate also gives the full sum as its sign value plus the tail sum. The first coordinate has sign value either $-1$ or $1$ (`FABL.signValue_eq_neg_one_or_one`).

If its sign value is $-1$, these identities give $k=r$. If the full sum is positive, then $k m+2$, so $r m+2$ and the tail sum is positive. If the full sum is negative, then $k m+1$, so $r m+1$ and the tail sum is negative. Here the integer thresholds follow from the full-sum formula and the fact that the sums are nonzero.

If the first coordinate's sign value is $1$, the identities instead give $k=r+1$. A positive full sum implies $k m+2$, hence $r m+1$ and a positive tail sum. A negative full sum implies $k m+1$, hence $r m$ and a negative tail sum. In both cases the tail and full sums therefore have the same sign. The sign-sum identity used above is the count formula `FABL.sum_signValue_eq_two_mul_positiveCoordinateCount_sub`. Finally, a nonnegative sum has threshold sign $1$, and a negative sum has threshold sign $-1` (`FABL.thresholdSign_of_nonneg`, `FABL.thresholdSign_of_neg`). Thus the lifted odd majority agrees with the threshold sign of the full sum whenever that sum is nonzero.

**Key facts.** `FABL.signValue_eq_neg_one_or_one`, `FABL.sum_signValue_eq_two_mul_positiveCoordinateCount_sub`, `FABL.thresholdSign_of_nonneg`, `FABL.thresholdSign_of_neg`.
