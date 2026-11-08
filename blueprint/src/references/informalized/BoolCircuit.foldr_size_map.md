<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Universal.lean :: BoolCircuit.foldr_size_map -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size of Equal-Size Circuits

**Claim.** If every circuit $g(a)$ has size $k$, then summing the sizes of $g(a)$ over a finite list $l$ gives $|l|k$.

**Proof.** Induct on $l$. For the empty list, both the sum and $|l|k$ are zero. For a head $a$ and tail $l'$, the sum is the size of $g(a)$ plus the tail sum. By hypothesis the head size is $k$, and by induction the tail sum is $|l'|k$. Thus the total is $k+|l'|k=(|l'|+1)k=|l|k$.
