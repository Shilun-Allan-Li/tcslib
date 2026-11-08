<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean :: Complexity.budgetValue_bits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value of the Binary Representation

**Claim.** For every natural number $n$, the little-endian value of its binary bit representation is $n$.

**Proof.** Proceed by the binary recursion that builds natural numbers from zero by appending a bit. At zero, the bit representation has value zero by the definition of `budgetValue`. For the recursive step, write the representation of the new number as the bits of the previous number followed by the new bit, using the binary representation append formula. The value of this appended word is obtained by applying the corresponding bit operation to the previous value; by the induction hypothesis that value is the previous number, so the result is exactly the number formed by the recursion.
