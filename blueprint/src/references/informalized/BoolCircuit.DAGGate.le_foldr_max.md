<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformCanon.lean :: BoolCircuit.DAGGate.le_foldr_max -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on a List Element by Its Folded Maximum

**Claim.** Every natural number occurring in a list is at most the result of folding maximum over that list starting from zero.

**Proof.** Induct on the list. The empty list has no member. For a list with head $b$ and tail $l$, an element is either $b$ or belongs to $l$. In the first case it is at most $\max(b,l.foldr\ max\ 0)$ by the left maximum bound. In the second case the induction hypothesis bounds it by the tail fold, which is at most the displayed maximum by the right maximum bound.
