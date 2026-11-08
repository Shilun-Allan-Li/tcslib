<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/DetModMath.lean :: Complexity.BinArith.getD_zero_eq_headD -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# The First Defaulted List Element

**Claim.** For any list $l$ of natural numbers, its element at index $0$, using $0$ as the default for an empty list, equals its head, using $0$ when the list is empty.

**Proof.** If $l$ is empty, both the defaulted element and defaulted head are $0$. If $l$ is nonempty, both are its first element.
