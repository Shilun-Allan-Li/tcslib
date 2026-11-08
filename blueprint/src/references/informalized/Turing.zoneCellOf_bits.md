<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Zone.lean :: Turing.zoneCellOf_bits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reconstruction from Cell Bits

**Claim.** For every optional Boolean cell value, encoding it by its presence bit and Boolean value (using false when absent), then reconstructing the optional value from those bits, returns the original value.

**Proof.** There are two cases. If the cell is absent, its presence bit is false, so reconstruction returns none, regardless of the default Boolean bit. If the cell is present with value $b$, its presence bit is true and its value bit is $b$, so reconstruction returns some $b$. In either case the reconstructed cell is the original one.
