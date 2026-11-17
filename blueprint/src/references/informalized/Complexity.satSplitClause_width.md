<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satSplitClause_width -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Width Bound for Split Clauses

**Claim.** Every clause produced by splitting any clause $C$ at cursor $n$ has at most three literals.

**Proof.** If $C$ is empty, the output consists of the empty clause, whose length is at most three. If $C$ is nonempty, splitting applies the chain construction to its head and remainder. The chain width result ($\texttt{satChain_width}$) bounds the length of every clause in that output by three, as required.

**Key facts.** `Complexity.satChain_width`.
