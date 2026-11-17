<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFHardTseitin.lean :: Complexity.TQBFHard.foldr_max_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on a Fold of Maxima

**Claim.** If every entry of a finite list of natural numbers is at most $B$, then folding maximum over the list, starting from zero, also gives a value at most $B$.

**Proof.** Induct on the list. For the empty list, the fold is zero, which is at most $B$. For a list with head $a$ and tail $L$, the fold is $\max(a,L.\mathrm{foldr}\ \max\ 0)$. The hypothesis bounds $a$ by $B$, and it bounds every entry of the tail by $B$; applying the induction hypothesis bounds the tail’s fold by $B$. The maximum of two numbers each at most $B$ is at most $B$.
