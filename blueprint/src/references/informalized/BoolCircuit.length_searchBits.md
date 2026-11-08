<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/KarpLiptonSearch.lean :: BoolCircuit.length_searchBits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of the search bits

**Claim.** For every Boolean list $y$ and natural number $j$, the search bits constructed from $y$ using the first $j$ circuits have length $j$.

**Proof.** Induct on $j$. At $j=0$, the search-bit list is empty. At the successor step, the construction appends one Boolean value—the evaluation of the next circuit—to the search-bit list for $j$. By induction that earlier list has length $j$, so the new list has length $j+1$.
