<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/NPReductions/SATTo3SAT.lean :: SATTo3SAT.buildChain_forced_false -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# False literals force the preceding auxiliary variable false

**Claim.** For a list of at least two literals, if every lifted literal is false and every clause in its chain is satisfied, then the auxiliary variable at index $j-1$ cannot be true.

**Proof.** Induct on the list, generalizing $j$. Lists of length less than two are excluded by the length hypothesis. If the list has exactly two literals, its chain is the single final clause: the negation of the auxiliary variable at index $j-1$ together with the two lifted literals. If that auxiliary variable were true, all three disjuncts would be false, contradicting satisfaction. For a longer list, its first, middle chain clause contains that same negated auxiliary literal, the first lifted literal, and the positive auxiliary literal at index $j$. Satisfaction, together with the assumed truth of the preceding auxiliary variable and falsity of the first lifted literal, forces the auxiliary variable at index $j$ to be true. The tail still has at least two literals, all its lifts remain false, and every clause in its chain is satisfied because those clauses occur in the original chain. Apply induction to the tail at counter $j+1$; its preceding auxiliary variable is exactly the one at index $j$, yielding a contradiction.
