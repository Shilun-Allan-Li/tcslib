<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Median.lean :: Randomized.countP_lt_add_countP_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Threshold Count Partition

**Claim.** For a finite list $l$ in a linearly ordered type and a threshold $x$, the number of entries strictly greater than $x$ plus the number less than or equal to $x$ is the length of $l$.

**Proof.** Proceed by induction on $l$. The equality is immediate for the empty list. For a list with head $a$ and tail $t$, the induction hypothesis handles the tail. If $x<a$, the head contributes one to the count of entries greater than $x$; otherwise it contributes one to the count of entries at most $x$. These cases are exhaustive by linearity of the order. The head therefore adds one to the sum of counts, exactly matching its contribution to the list length.
