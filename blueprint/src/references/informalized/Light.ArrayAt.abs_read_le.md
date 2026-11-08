<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/ArrayAt.lean :: Light.ArrayAt.abs_read_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on an Array Read

**Claim.** Under the stated array conditions, $|\mu(a+i)|\le U$ whenever $i<N$.

**Proof.** For $i<N$, the length condition gives $i<\operatorname{length}(l)$. The segment condition identifies the array value $\mu(a+i)$ with the list entry at position $i$. Every in-range list entry has absolute value at most $U$ (`Light.AbsLe.getElem`), so the same bound holds for this array value.

**Key facts.** `Light.AbsLe.getElem`.
