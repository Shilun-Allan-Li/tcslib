<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satChain_complete -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Completeness of the Clause-Splitting Chain

**Claim.** If all variables in the clause $h::R$ have indices below $n$ and that clause is satisfied by $a$, then an assignment $a'$ agreeing with $a$ below $n$ satisfies the CNF formula produced by the clause-splitting chain from $h$, remainder $R$, and cursor $n$.

**Proof.** Induct on the remainder, generalizing the head, cursor, and assignment. When the remainder has fewer than three literals, the chain produces the original single clause, so the given assignment itself is a witness. Otherwise write the first three literals after the head as $b,c,d$. The splitting-step extension lemma (`satChain_extend_step`) gives an assignment $a_1$ agreeing with $a$ below $n$, satisfying the new link clause $[h,b,(n,\mathrm{true})]$, and satisfying the continuation clause $[(n,\mathrm{false}),c,d,\ldots]$. Every variable in this continuation has index below $n+1$: old indices are below $n$, while the new variable has index $n$. Apply the induction hypothesis to that continuation with cursor $n+1$ to obtain $a_2$ satisfying the rest of the chain and agreeing with $a_1$ below $n+1$. In particular, $a_2$ agrees with $a_1$ on the variables of the link clause, whose old indices are below $n$ and whose added index is $n$. The clause-congruence lemma (`satClause_congr`) therefore transfers satisfaction of the link clause from $a_1$ to $a_2$. The two agreements also show that $a_2$ agrees with $a$ below $n$. Together, satisfaction of the link clause and the recursively produced chain clauses gives satisfaction of the whole CNF chain.

**Key facts.** `Complexity.satChain_extend_step`, `Complexity.satClause_congr`.
