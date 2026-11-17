<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Median.lean :: Randomized.countP_le_eq_countP_lt_add_count -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counting Entries at a Threshold

**Claim.** For any list $l$ in a linearly ordered type and any element $y$, the number of entries at most $y$ is the number strictly less than $y$ plus the number equal to $y$.

**Proof.** Induct on the list. The identity is immediate for the empty list. For a list with first entry $a$ and tail $t$, use the induction hypothesis for $t$ and divide into the three possibilities given by linearity: $a<y$, $a=y$, or $y<a$. In the first case, $a$ contributes one to both the at-most and strictly-less counts; in the equality case, it contributes one to the at-most count and the equality count; in the last case, it contributes to none of them. Thus the first entry’s contribution agrees on both sides in every case, and the tail identity completes the proof.
