<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/TreeDAG.lean :: BoolCircuit.unfoldGate_size_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size Bound After Gate Unfolding

**Claim.** If a well-formed gate has at most $k$ arguments and each circuit assigned to one of its arguments has size at most $B$, then its unfolding at any polarity has size at most $1+kB$.

**Proof.** Write the gate as its kind and argument list. For an AND or OR gate, unfolding creates one node with one assigned circuit as a child for each argument. The size of a node is one plus the sum of its children's sizes (`TreeCircuit.size_node`). The sum over the mapped argument list is at most the argument-list length times $B$, since every assigned circuit has size at most $B$ (`sumSize_map` and `sum_le_card_mul`). As the argument-list length is at most $k$, this gives a size of at most $1+kB`.

For a NOT gate, well-formedness says its argument list has exactly one element, say $a$. Unfolding returns the assigned circuit for $a$ at the opposite polarity. Its size is at most $B$ by hypothesis. The singleton list also implies $1\le k$, so $B\le 1+kB$, giving the claimed bound.

**Key facts.** `BoolCircuit.TreeCircuit.size_node`, `BoolCircuit.sumSize_map`, `BoolCircuit.sum_le_card_mul`.
