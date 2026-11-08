<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Formulas/CNF.lean :: Complexity.le_foldr_max_of_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# List entries are bounded by the folded maximum

**Claim.** Every natural number occurring in a finite list $s$ is at most the right fold of maximum over $s$ with initial value $0$.

**Proof.** Induct on the list. The empty-list case has no member. For a list with head $m$ and tail $s$, a member is either $m$ or belongs to the tail. In the first case, it is at most $\max(m,s\texttt{.foldr max 0})$ by the left-max bound. In the second, induction bounds it by the tail fold, which is at most the whole fold by the right-max bound; transitivity gives the result.
