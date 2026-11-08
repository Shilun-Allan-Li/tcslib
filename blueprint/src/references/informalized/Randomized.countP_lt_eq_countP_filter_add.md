<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Median.lean :: Randomized.countP_lt_eq_countP_filter_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Filtered Threshold Count

**Claim.** If $x<y$, the number of entries of $l$ strictly less than $y$ is the sum of the number that are both greater than $x$ and less than $y$ and the number less than or equal to $x$.

**Proof.** Induct on the list. The empty case has both sides zero. For a head $a$ and tail, split according to whether $x<a$. If so, the head appears in the filtered list; its contribution to the count below $y$ is the same on both sides, and the tail equality follows from induction. If not, then $a\le x<y$, so the head is below $y$ and contributes once to the count on the left and once to the count of entries at most $x$ on the right; it does not enter the filtered list. In either case the head contributions agree, and the induction hypothesis supplies the tail equality.
