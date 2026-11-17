<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGFanin.lean :: BoolCircuit.le_foldr_max₂ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Maximum Bound for List Values

**Claim.** If $a$ occurs in a list $l$ of natural numbers, then $f(a)$ is at most the maximum of the values of $f$ on the entries of $l$, with $0$ included in the maximum.

**Proof.** Induct on $l$. The empty-list case is impossible because it has no entries. For a list with head $b$ and tail $l'$, its mapped fold is $\max(f(b),M')$, where $M'$ is the corresponding fold for $l'$. If $a=b$, then $f(a)$ is at most this maximum by the defining property of a maximum. If $a$ occurs in $l'$, the induction hypothesis gives $f(a)\le M'$, and hence $f(a)\le\max(f(b),M')$.
