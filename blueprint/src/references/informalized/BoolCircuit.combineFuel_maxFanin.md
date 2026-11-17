<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/TreeNCAC.lean :: BoolCircuit.combineFuel_maxFanin -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fanin Bound for Recursive Combination

**Claim.** If a finite list $cs$ of Boolean circuit trees has length at most $k$, then recursively combining it with fuel $k$ has maximum fanin at most the larger of $2$ and the largest fanin among the circuits in $cs$, with the empty-list maximum equal to $0$.

**Proof.** Proceed by induction on the fuel and split according to the list shape. The empty-list cases produce an empty gate, whose fanin is bounded by $2$; a singleton is returned unchanged, and its fanin is bounded by the maximum fanin of the list. A nonempty list cannot occur with zero fuel. For a list with at least two entries, pair consecutive circuits into binary gates and apply the induction hypothesis to the resulting list with one less unit of fuel. Pairing shortens the list according to the length formula $(|cs|+1)/2$ (`length_pairUp`), so the reduced list satisfies the required fuel bound. The largest fanin among the paired circuits is at most the larger of $2$ and the original list's largest fanin (`maxFaninL_pairUp`), since each newly introduced gate has two children. Hence the inductive bound on the recursively combined paired list gives the required bound. Here the fanin of a node is the larger of its number of children and the largest child fanin (`TreeCircuit.maxFanin_node`); the list maximum is computed by taking successive maxima, with empty value $0$ (`TreeCircuit.maxFaninL_cons`, `TreeCircuit.maxFaninL_nil`).

**Key facts.** `BoolCircuit.TreeCircuit.maxFaninL_nil`, `BoolCircuit.TreeCircuit.maxFaninL_cons`, `BoolCircuit.TreeCircuit.maxFanin_node`, `BoolCircuit.length_pairUp`, `BoolCircuit.maxFaninL_pairUp`.
