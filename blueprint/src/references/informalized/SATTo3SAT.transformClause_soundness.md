<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/NPReductions/SATTo3SAT.lean :: SATTo3SAT.transformClause_soundness -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Soundness of Clause Transformation

**Claim.** If every three-literal clause produced by transforming a clause is satisfied by an assignment to the original and auxiliary variables, then the original clause contains a literal satisfied by the assignment restricted to original variables.

**Proof.** Suppose instead that every literal of the original clause is false under the restricted assignment. The mapping `ml` sends each literal to the corresponding literal on its original-variable vertex, so every mapped literal is false as well. If the clause is empty, its encoding contains both the triple consisting of three copies of an auxiliary variable and the triple of three copies of its negation. Satisfying both would require that auxiliary variable to be both true and false, a contradiction. For clauses of length one, two, or three, the single encoded clause is satisfied only if one of its original literals is true, contradicting the assumption. For a clause of length at least four, the first encoded clause forces the first auxiliary variable in the chain to be true, since its first two literals are false. The remaining literals are all false, and every clause in the chain is satisfied by hypothesis. The chain-forcing lemma (`buildChain_forced_false`) says these conditions are incompatible: a satisfied chain with all its mapped literals false cannot have its initial auxiliary variable true. This contradiction proves the claim.

**Key facts.** `SATTo3SAT.buildChain_forced_false`.
