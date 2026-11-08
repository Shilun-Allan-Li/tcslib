<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/NPReductions/SATTo3SAT.lean :: SATTo3SAT.buildChain_all_satisfied -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Satisfaction of the chain clauses

**Claim.** If some literal of the original clause is true, then every 3-clause in the chain built from the suffix after the first $j+1$ literals is satisfied, for each $j\ge1$, under the stated auxiliary-variable and lifting rules.

**Proof.** First note two consequences of the auxiliary valuation rule: if the all-false-prefix condition at index $k$ fails, then the negated auxiliary literal at index $k$ is true; if that condition holds, then the positive auxiliary literal at index $k$ is true. Now induct on the suffix list, generalizing the counter $j$. The empty suffix produces no chain clauses. For a suffix of length one or two, the chain consists of its final clause, whose first literal is the negation of the preceding auxiliary variable. If that auxiliary variable is false, this first literal satisfies the clause. If it is true, the prefix through position $j+1$ must consist entirely of false literals. The assumed true literal of the original clause therefore cannot lie in that prefix; since the whole clause is the prefix followed by the one- or two-literal suffix, the true literal lies in the suffix. Its lifted literal satisfies the final clause by the truth-preservation property of the lifting map.

For a suffix of length at least three, consider the first chain clause. If the preceding auxiliary variable is false, its negation satisfies the clause. Otherwise, if the first literal of the suffix is true, its lift satisfies the clause. In the remaining case, that first literal is false and the preceding auxiliary variable is true. The prefix condition at index $j-1$ says the first $j+1$ literals are false; the prefix-splitting identity, which follows from the dropped suffix beginning with the first suffix literal (`List.take_succ_of_drop_cons`), then shows that the all-false-prefix condition holds at index $j$. Hence the positive auxiliary literal at index $j$ satisfies this chain clause. Apply the induction hypothesis to the remaining suffix with counter $j+1$: it is the original clause with its first $j+2$ entries dropped, and the counter still meets the required lower bound. This establishes satisfaction of every remaining chain clause.

**Key facts.** `SATTo3SAT.List.take_succ_of_drop_cons`.
