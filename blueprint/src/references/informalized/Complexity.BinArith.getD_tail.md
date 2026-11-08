<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/DetModMath.lean :: Complexity.BinArith.getD_tail -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Indexing a List Tail

**Claim.** For any list $l$ of natural numbers and any natural number $j$, the element of the tail of $l$ at index $j$, using $0$ as the default when that index is out of range, equals the element of $l$ at index $j+1$ with the same default.

**Proof.** Split on whether $l$ is empty or has a head and tail. For the empty list, both expressions use the default value $0$. For a nonempty list, the tail's element at index $j$ is exactly the original list's element at index $j+1$, including the out-of-range default.
