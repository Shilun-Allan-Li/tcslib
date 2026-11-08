<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyGadget.lean :: BoolCircuit.ofFn_getD_eq_map -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mapped list reconstruction

**Claim.** If a list $l$ of natural numbers has length $m$, then listing $f(l_i)$ for indices $i=0,\ldots,m-1$, reading list entries with default value $0$, gives the list obtained by mapping $f$ over $l$.

**Proof.** Replace $m$ by the given length of $l$. Both lists have the same length. At each valid index, the reconstructed list contains $f$ applied to the value of $l$ at that index; because the index is within the list's length, the default value is not used. This is exactly the entry at that index in the mapped list, so the lists are equal.
