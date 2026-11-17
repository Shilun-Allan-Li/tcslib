<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Encoding.lean :: BoolCircuit.gateClauses_flatten_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of the Gate Clauses

**Claim.** For a Boolean value $b$ and a finite list $cs$ of circuit trees, the total number of literal occurrences in the clauses associated with $b$ and $cs$ is $3|cs|+1$.

**Proof.** First, for any fixed literal $x$ and map $g$ from circuit trees to literals, a list of $r$ trees contributes $2r$ literal occurrences to the flattened list of two-literal clauses $[x,g(c)]$. This follows by induction on the list: the empty list contributes zero, and each added tree contributes exactly two occurrences. Now split into the two values of $b$. In either case, the first clause contains one distinguished literal together with one mapped literal for each tree, so its length is $|cs|+1$. The remaining $|cs|$ clauses each have two literals, contributing $2|cs|$ in total by the auxiliary count. Adding these gives $3|cs|+1$.
