<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Encoding.lean :: BoolCircuit.tseitin_flatten_length_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tseitin Flattening Length Bound

**Claim.** For every Boolean circuit tree $C$ on $n$ variables, the length of the flattened Tseitin formula associated with $C$, plus $3$, is at most $7$ times the size of $C$.

**Proof.** Proceed by structural induction on the circuit. For a literal, its Tseitin formula consists of two clauses, and direct evaluation of the size and flattened length verifies the bound. For a node with children $c_1,\ldots,c_r$, first establish the list estimate: if each child satisfies $\mathrm{length}(c_i.\mathrm{tseitin.flatten})+3\le7\,\mathrm{size}(c_i)$, then summing these inequalities gives the flattened length of all child formulas plus $3r$ at most seven times the sum of the child sizes. The induction hypotheses provide these child bounds. The node's gate clauses have flattened length $3r+1$ (\texttt{BoolCircuit.gateClauses\_flatten\_length}). Adding this to the child contribution, and accounting for the node's size, gives the desired bound by arithmetic.

**Key facts.** `BoolCircuit.TreeCircuit.ind`, `BoolCircuit.gateClauses_flatten_length`.
