<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/TreeNCAC.lean :: BoolCircuit.combineFuel_depth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth Bound for Recursive Combination

**Claim.** If a finite list $cs$ of Boolean circuit trees has length at most $k$, then recursively combining it with fuel $k$ has depth at most the maximum depth in $cs$ plus $\operatorname{clog}_2(|cs|)+1$, with the empty-list maximum taken to be $0$.

**Proof.** Proceed by induction on the fuel and split according to the list shape. The empty list and singleton list give the stated bound directly: the empty case is a single gate, while the singleton case returns the circuit itself and the maximum depth of the list is its depth. A nonempty list cannot occur with zero fuel because of the length hypothesis. For a list with at least two entries, pair consecutive circuits into new binary gates and recursively combine the resulting shorter list using one less unit of fuel. The length formula for pairing, $(|cs|+1)/2$ (`length_pairUp`), shows that the new list fits within the reduced fuel. By the inductive bound, its combination has depth at most its maximum input depth plus the ceiling logarithm of its length plus one. Pairing increases the maximum depth by at most one (`maxDepth_pairUp`), and for a list of length at least two the ceiling logarithm of the original length is exactly one more than that of the paired list. Combining these estimates gives the claimed bound. The node-depth formula, $1$ plus the maximum depth of its children (`TreeCircuit.depth_node`), and the empty and cons formulas for list maximum depth (`TreeCircuit.maxDepth_nil`, `TreeCircuit.maxDepth_cons`) account for the base cases.

**Key facts.** `BoolCircuit.TreeCircuit.depth_node`, `BoolCircuit.TreeCircuit.maxDepth_nil`, `BoolCircuit.TreeCircuit.maxDepth_cons`, `BoolCircuit.length_pairUp`, `BoolCircuit.maxDepth_pairUp`.
