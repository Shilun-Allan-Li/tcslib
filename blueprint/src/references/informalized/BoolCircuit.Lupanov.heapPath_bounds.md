<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LupanovGates.lean :: BoolCircuit.Lupanov.heapPath_bounds -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounds for Heap Path Values

**Claim.** For every depth $l$, the heap path value lies between $2^l$ inclusive and $2^{l+1}$ exclusive.

**Proof.** Proceed by induction on $l$. At depth zero, the path value is $1$, which lies in $[1,2)$. For the induction step, write the previous value as $H$. By induction, $2^l\le H<2^{l+1}$. The next value is $2H+b$, where the added Boolean coordinate, interpreted as a natural number, is either $0$ or $1$. Hence it is at least $2\cdot 2^l=2^{l+1}$ and at most $2(H)+1<2\cdot 2^{l+1}$, so it lies in $[2^{l+1},2^{l+2})$. This argument also covers coordinates beyond the vector’s range, since those are defined to be false.
