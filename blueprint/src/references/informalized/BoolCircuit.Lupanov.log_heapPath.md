<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LupanovGates.lean :: BoolCircuit.Lupanov.log_heapPath -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Heap Path Logarithm

**Claim.** The base-$2$ logarithm of the heap path value at depth $l$ with offset $o$ is $l$.

**Proof.** The heap path bounds place its value in the interval $[2^l,2^{l+1})$. The characterization of the integer base-$2$ logarithm says that any natural number in this interval has logarithm $l$. Applying it gives the claimed equality; the bounds used are precisely `BoolCircuit.Lupanov.heapPath_bounds`.

**Key facts.** `BoolCircuit.Lupanov.heapPath_bounds`.
