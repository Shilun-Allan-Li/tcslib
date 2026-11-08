<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/TreeNCAC.lean :: BoolCircuit.combineFuel_size -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size Bound for Recursive Combination

**Claim.** For every natural number $k$, recursively combining a finite list $cs$ of Boolean circuit trees with fuel $k$ yields a circuit whose size is at most the sum of the sizes in $cs$, plus $|cs|+1$.

**Proof.** Proceed by induction on the fuel and split by the list shape. With zero fuel, the result is one gate whose size is one plus the sum of the input sizes. With positive fuel, the empty-list result has size one, and the singleton result is the sole input circuit; both satisfy the bound directly. For a list of at least two circuits, pair consecutive entries and invoke the induction hypothesis on the paired list. Pairing does not increase the sum of circuit sizes plus the list length (`sumSize_pairUp`): each binary gate adds one node, while the pairing reduces the number of list entries enough to offset those added nodes. Applying the induction estimate to the paired list and then this inequality yields the asserted bound. The node size formula is one plus the sum of its children's sizes (`TreeCircuit.size_node`); the sum over a list has the usual cons and empty-list values (`TreeCircuit.sumSize_cons`, `TreeCircuit.sumSize_nil`).

**Key facts.** `BoolCircuit.TreeCircuit.size_node`, `BoolCircuit.TreeCircuit.sumSize_nil`, `BoolCircuit.TreeCircuit.sumSize_cons`, `BoolCircuit.sumSize_pairUp`.
