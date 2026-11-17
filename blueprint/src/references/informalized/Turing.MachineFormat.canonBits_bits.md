<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.MachineFormat.canonBits_bits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Canonical Expansion Has a True Final Bit

**Claim.** For every natural number, its binary expansion has true as its last symbol, treating the empty expansion as having last symbol true.

**Proof.** Use binary recursion from one. At the base cases, the binary expansions have true last-symbol test. For the inductive step, write the number as a nonzero value formed by appending a low bit to a positive tail. The tail’s binary expansion cannot be empty: otherwise `codeBitsNat_bits` would make the tail zero, contrary to its positivity. The binary-expansion append formula then expresses the current expansion as the tail expansion followed by the low bit. Since the tail expansion is nonempty, appending that bit makes it the last symbol, and the recursion hypothesis gives that it is true. This proves the property for every natural number.

**Key facts.** `Turing.codeBitsNat_bits`.
