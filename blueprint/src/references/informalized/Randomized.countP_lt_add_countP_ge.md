<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Median.lean :: Randomized.countP_lt_add_countP_ge -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Threshold Count Partition

**Claim.** For a finite list $l$ in a linearly ordered type and a threshold $x$, the number of entries strictly below $x$ plus the number greater than or equal to $x$ is the length of $l$.

**Proof.** Proceed by induction on $l$. For the empty list, all three quantities are zero. For a list with head $a$ and tail $t$, the induction hypothesis gives the equality for $t$. The head contributes exactly one to the first count when $a<x$, and otherwise contributes exactly one to the second count, since linearity of the order gives $x\le a$. Thus the two head contributions sum to one; adding the tail equality yields the length of the whole list.
