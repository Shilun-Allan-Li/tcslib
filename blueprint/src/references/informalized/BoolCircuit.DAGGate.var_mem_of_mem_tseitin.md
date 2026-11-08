<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGCircuitSat.lean :: BoolCircuit.DAGGate.var_mem_of_mem_tseitin -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Variables in Tseitin clauses

**Claim.** For every natural number $z$ and gate $g$, each literal in each clause of the Tseitin formula for $g$ with output variable $z$ has a variable that is either $z$ or one of the argument indices of $g$.

**Proof.** Write the gate as a kind together with its argument list, and split according to the list’s length. With no arguments, every clause contains only the output variable $z$. With one or two arguments, the displayed clauses in the definition of the Tseitin formula contain literals only on $z$ and the listed argument indices; checking each gate kind gives the claim. If there are at least three arguments, the formula is empty, so there are no clauses or literals to check.
