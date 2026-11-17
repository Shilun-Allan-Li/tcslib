<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satChain_extend_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Extending an Assignment at a Splitting Step

**Claim.** If the clause $h::b::R$ is satisfied by $a$ and all its variables have indices below $n$, one can change the assignment only at index $n$ to satisfy both the link clause $[h,b,(n,\mathrm{true})]$ and the continuation clause $[(n,\mathrm{false})::R]$.

**Proof.** Define $a'$ to agree with $a$ except at $n$, where its value is the truth value of the tail clause $R$ under $a$. Since every variable in $h$, $b$, and $R$ has index below $n$, this change preserves the values of all their variables. Consequently $R$ has the same truth value under $a'$ as under $a$ (`satClause_congr`). If $R$ was true, the new variable is true: the continuation clause is satisfied by its negative literal, while the link clause is satisfied by its positive literal. If $R$ was false, the original clause's satisfaction forces at least one of $h$ or $b$ to be true, so the link clause is satisfied regardless of the new variable; the new variable is false, making the negative literal satisfy the continuation clause. In either case $a'$ agrees with $a$ below $n$ and satisfies both clauses.

**Key facts.** `Complexity.satClause_congr`.
