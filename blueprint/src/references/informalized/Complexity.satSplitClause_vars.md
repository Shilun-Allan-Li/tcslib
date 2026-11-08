<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satSplitClause_vars -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Variable Bound After Clause Splitting

**Claim.** If every variable index in a clause $C$ is less than $n$, then every variable index in every clause produced by splitting $C$ at $n$ is less than the returned cursor.

**Proof.** For the empty clause, splitting returns the formula containing the empty clause and leaves the cursor at $n$. There are no literals in that output clause, so the variable bound holds vacuously. For a nonempty clause, the split is the chain construction on its head and remainder. The chain variable-bound result ($\texttt{satChain_vars}$), applied with the given hypothesis on all literals of $C$, yields the bound for every output clause relative to the returned cursor.

**Key facts.** `Complexity.satChain_vars`.
