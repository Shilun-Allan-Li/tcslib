<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGTransform.lean :: BoolCircuit.foldr_max_le' -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on a List Maximum

**Claim.** If every value $f(a)$ for $a$ in a finite list $l$ is at most $B$, then the maximum of those values, with empty-list value $0$, is at most $B$.

**Proof.** Induct on $l$. For the empty list the fold is $0\le B$. If $l$ has head $a$ and tail $l'$, its folded maximum is $\max(f(a),M')$, where $M'$ is the folded maximum for $l'$. The hypothesis bounds $f(a)$ by $B$, and its restriction to the tail together with induction bounds $M'$ by $B$. Hence their maximum is at most $B$.
