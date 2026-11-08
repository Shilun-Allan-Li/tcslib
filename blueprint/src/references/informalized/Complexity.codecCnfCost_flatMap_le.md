<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.codecCnfCost_flatMap_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cost of a flattened CNF list

**Claim.** If every CNF assigned to an element occurring in a list $X$ has cost at most $B$, then the cost of their concatenation in list order is at most $|X|B$.

**Proof.** Induct on $X$. For the empty list, the concatenation is empty and has cost zero. For a list with head $x$ and tail $X'$, flattening gives $f(x)$ followed by the flattening of $X'$. Cost is additive under concatenation (`Complexity.codecCnfCost_append`), so the total cost is the cost of $f(x)$ plus the tail cost. The hypothesis bounds the first term by $B$, and the induction hypothesis bounds the second by $|X'|B$. Their sum is $(|X'|+1)B=|X|B$.

**Key facts.** `Complexity.codecCnfCost_append`.
