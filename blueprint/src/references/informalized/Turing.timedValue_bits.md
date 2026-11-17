<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timedValue_bits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value of the Binary Representation

**Claim.** For every natural number $t$, the little-endian value of the binary representation of $t$ is $t$.

**Proof.** Proceed by the binary recursion for natural numbers. At zero, the bit list is empty and its value is $0$. In the recursive bit case, the bit representation is obtained by appending the new bit to the representation of the smaller number. By the induction hypothesis, the existing representation evaluates to that smaller number; the value of appending a bit is the operation of adjoining that bit via $\operatorname{bit}$ (`Nat.bits_append_bit`). Applying this operation to both sides of the induction equality shows that the extended representation evaluates to the corresponding recursively constructed number.
