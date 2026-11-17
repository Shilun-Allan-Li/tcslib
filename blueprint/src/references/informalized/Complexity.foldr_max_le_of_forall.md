<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Formulas/CNF.lean :: Complexity.foldr_max_le_of_forall -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Termwise bound on a list maximum

**Claim.** If every member of a finite list of natural numbers is at most $n$, then folding maximum over the list from the right with initial value $0$ gives a result at most $n$.

**Proof.** Induct on the list. For the empty list the fold is $0\le n$. For a list with head $k$ and tail $s$, the fold is the maximum of $k$ and the fold over $s$. The hypothesis bounds $k$ by $n$, and it bounds every member of $s$ by $n$, so the induction hypothesis bounds the tail fold by $n$. The maximum of two numbers each at most $n$ is at most $n.
