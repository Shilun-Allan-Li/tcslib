<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/TreeDAG.lean :: BoolCircuit.le_foldr_max -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound by the Maximum of Mapped List Values

**Claim.** If $a$ belongs to a list $l$, then $f(a)$ is at most the maximum of the values of $f$ on entries of $l$, with $0$ included in the maximum.

**Proof.** Induct on the list. The empty-list case cannot contain $a$. For a list with head $b$ and tail $l$, its mapped maximum is the maximum of $f(b)$ and the mapped maximum for the tail. If $a=b$, then $f(a)$ is at most this maximum by the left-hand bound for a maximum. Otherwise $a$ belongs to the tail; the induction hypothesis bounds $f(a)$ by the tail maximum, which in turn is at most the whole-list maximum by the right-hand bound for a maximum.
