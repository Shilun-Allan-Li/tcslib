<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/TreeDAG.lean :: BoolCircuit.foldr_max_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on a Folded Maximum

**Claim.** If every value $f(a)$ for $a$ in a finite list $l$ is at most $B$, then folding the values $f(a)$ with maximum, starting at $0$, gives a result at most $B$.

**Proof.** Induct on the list. For the empty list, the fold is $0$, which is at most the natural number $B$. For a list with head $a$ and tail $l'$, the fold is the maximum of $f(a)$ and the fold over $l'$. The hypothesis bounds the first term by $B$, while the induction hypothesis bounds the tail fold by $B$, using the same pointwise assumption restricted to $l'$. The maximum of two numbers at most $B$ is at most $B.
