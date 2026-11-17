<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGFanin.lean :: BoolCircuit.foldr_max_le₂ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on a List Maximum

**Claim.** If every value $f(a)$ for $a$ in a finite list $l$ is at most $B$, then the maximum of those values, with empty-list value $0$, is at most $B$.

**Proof.** Induct on $l$. The empty-list fold is $0\le B$. For a head $a$ and tail $l'$, the fold is $\max(f(a),M')$, where $M'$ is the fold for the tail. The pointwise hypothesis bounds $f(a)$ by $B$, and its restriction to $l'$ plus induction bounds $M'$ by $B$. Therefore their maximum is at most $B$.
