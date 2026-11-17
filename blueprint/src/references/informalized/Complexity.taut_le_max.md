<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Tautology.lean :: Complexity.taut_le_max -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# List Entries Bounded by Fold Maximum

**Claim.** Every natural number occurring in a list is at most the right fold of maximum over that list with initial value zero.

**Proof.** Induct on the list. The empty list has no member. For a list with head $m$ and tail $s$, a member is either $m$, which is at most $\max(m,s.\mathrm{foldr}(\max,0))$, or is a member of $s$. In the latter case the induction hypothesis bounds it by the tail fold, and the tail fold is at most that same maximum. Thus every member is bounded by the fold for the whole list.
