<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/HardWire.lean :: BoolCircuit.foldr_max_le_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pointwise Slack for List Maxima

**Claim.** If $p(a)\le q(a)+1$ for every $a$ in a finite list $l$, then the folded maximum of the $p$-values is at most one more than the folded maximum of the $q$-values.

**Proof.** Induct on the list. The empty-list maxima are both $0$, so the claimed inequality holds. For a head $a$ and tail $l'$, the induction hypothesis bounds the tail maximum of $p$ by one plus the tail maximum of $q$. Also, $p(a)\le q(a)+1\le M_q+1$, where $M_q$ is the folded maximum of the $q$-values on the whole list, since $q(a)$ is at most that maximum. The tail maximum for $q$ is likewise at most $M_q$, so the induction bound gives the tail maximum for $p$ at most $M_q+1$. Both entries in the head-tail maximum for $p$ are therefore at most $M_q+1$, proving the result.
