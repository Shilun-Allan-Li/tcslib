<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/StatementCode.lean :: Light.maxOf_le_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Characterizing a list maximum bound

**Claim.** The recursively defined maximum of $f$ over a list is at most $F$ exactly when every value of $f$ on that list is at most $F$.

**Proof.** Induct on the list. For the empty list, its maximum is $0$, which is at most the natural number $F$, and there are no entries to check. For a list with head $x$ and tail $l$, its maximum is $\max(f(x),\maxOf(f,l))$. This is at most $F$ exactly when both $f(x)\le F$ and the tail maximum is at most $F$. By the induction hypothesis, the latter is equivalent to the bound holding for every entry of the tail; together with the head bound, this is precisely the pointwise bound on the whole list.
