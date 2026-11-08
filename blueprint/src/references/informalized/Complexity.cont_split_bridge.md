<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.cont_split_bridge -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement of Split Searches

**Claim.** For natural numbers $C,c,m$, the two bounded searches return the same least solution of $n+C(n+1)^c=m$, or both return no value when there is no solution.

**Proof.** Both searches scan the same list, from $0$ through $m$, and `List.find?` selects the first entry satisfying its predicate. In the first search the predicate is $i+C(i+1)^c=m$; in the second it is $n+(C+1)(n+1)^c=m$. These predicates agree by unfolding the definitions and simplifying the natural-number arithmetic, so the searches are definitionally equal.
