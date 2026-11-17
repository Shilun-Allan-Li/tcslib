<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitSat.lean :: BoolCircuit.TreeCircuit.tseitin_length_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tseitin formula length bound

**Claim.** For every Boolean circuit $C$, the length of its Tseitin formula is strictly less than $3\,\mathrm{size}(C)$.

**Proof.** Proceed by structural induction on $C$. For a literal, the Tseitin formula and circuit size are given by their base definitions, and the claimed strict inequality follows directly. Now let $C$ be a node with children $c_1,\ldots,c_m$, and assume the bound holds for every child. First prove a list estimate: the total length of the concatenated child Tseitin formulas, plus the number $m$ of children, is at most three times the sum of their sizes. This follows by induction on the child list: the induction hypothesis handles the remaining children, and the strict bound for the first child supplies its contribution. The clauses added for the parent gate have length $m+1$, whether the node is an AND or an OR gate. Thus the full Tseitin formula has length equal to the child-formula lengths plus $m+1$. The node's size is one plus the sum of the child sizes, so the list estimate gives the desired strict bound after this parent contribution is included.

**Key facts.** `BoolCircuit.TreeCircuit.ind`.
