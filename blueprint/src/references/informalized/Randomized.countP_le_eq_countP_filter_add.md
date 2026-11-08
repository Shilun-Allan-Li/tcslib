<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Median.lean :: Randomized.countP_le_eq_countP_filter_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Partition at a Threshold

**Claim.** If $x<y$, the number of entries of $l$ at most $y$ equals the number among entries strictly greater than $x$ that are at most $y$, plus the number of entries at most $x$.

**Proof.** Induct on the list. The empty list has all three counts equal to zero. For a list with first entry $a$ and tail $t$, split into two cases. If $x<a$, the first entry belongs to the filtered list of entries greater than $x$; its contribution to the count at most $y$ is included there exactly when $a\le y$. The tail satisfies the claimed identity by induction. If instead $a\le x$, then $a<y$, so the first entry contributes one to the total count at most $y$ and one to the count at most $x$, but contributes nothing to the filtered count. The tail identity again follows by induction. In either case, adding the first entry’s contributions proves the formula.
