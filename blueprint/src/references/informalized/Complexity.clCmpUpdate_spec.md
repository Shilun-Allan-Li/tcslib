<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clCmpUpdate_spec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Comparator Invariant Under One-Column Update

**Claim.** The comparator invariant for the four words and registers holds exactly when it holds after one column update on the word tails, using each word’s first bit or zero if it is empty.

**Proof.** For each word, its little-endian value is twice the value of its tail plus the bit at its head, treating a missing head as zero (`Complexity.clNum_head`). For each pair of input bits and its carry, the column-adder identity says that their sum is twice the new carry plus the output bit (`Complexity.clAddColumn_value`). Applying these identities to the two sides of the invariant expresses the original sum equality as an equality of two numbers of the form $2A+u$, where $u$ is a bit. Such an equality holds exactly when the output bits agree and the corresponding $A$ values agree: parity gives equality of the bits, and cancellation of the factor of two gives equality of the remaining values. The output-bit agreement, together with the previous equality flag, is exactly the updated flag; equality of the remaining values is the invariant for the tails and updated carries. This proves the equivalence in both directions.

**Key facts.** `Complexity.clNum_head`, `Complexity.clAddColumn_value`.
