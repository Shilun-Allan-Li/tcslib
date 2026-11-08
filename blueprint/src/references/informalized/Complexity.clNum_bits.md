<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clNum_bits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value of a Binary Representation

**Claim.** For every natural number $n$, the little-endian value of the binary representation of $n$ is $n$.

**Proof.** Proceed by the binary recursion for natural numbers. At zero, the binary representation has value zero. In the recursive bit case, the representation of the new number is obtained by appending the corresponding bit to the representation of the preceding number. The value of that appended representation is the natural-number bit operation applied to the old value. By induction the old value is the preceding number, and the binary recursion defines the new number by that same bit operation. Hence the represented value is the new number.
