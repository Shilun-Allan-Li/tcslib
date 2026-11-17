<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Lupanov.lean :: BoolCircuit.Lupanov.assemble_heapPath -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reconstruction from Heap Paths

**Claim.** For \(k\le n\), assembling the heap-path indices of \(x\) on its first \(n-k\) and last \(k\) coordinates recovers \(x\).

**Proof.** Fix a coordinate \(i\) of \(x\), and split according to whether \(i<n-k\). In the first block, the heap-path bound (\texttt{BoolCircuit.Lupanov.heapPath_bounds}) ensures that adding back the subtracted leading power recovers the first block’s heap-path number. Its bit-extraction property (\texttt{BoolCircuit.Lupanov.testBit_heapPath}) says that the bit used by the assembly at position \(i\) is exactly the corresponding input bit. In the second block, the same bound and bit-extraction property, now for the heap path starting at coordinate \(n-k\), identify the selected bit with the input at coordinate \(iesizebox{!}{0pt}{}\). Thus the assembled function agrees with \(x\) at every coordinate, so the two functions are equal.

**Key facts.** `BoolCircuit.Lupanov.heapPath_bounds`, `BoolCircuit.Lupanov.testBit_heapPath`.
