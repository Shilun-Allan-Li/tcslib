<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.MachineFormat.canonBitsOK_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Characterization of Canonical Boolean Words

**Claim.** A Boolean word has true as its last symbol, with the empty word treated as having last symbol true, exactly when it is the binary expansion of the number obtained by folding its symbols from right to left as binary digits, starting at zero.

**Proof.** If the word’s last-symbol test is true, `canonBits_of_last` says that the binary expansion of its fold value is the word itself. This is the required equality. Conversely, suppose the word equals that binary expansion. Applying the last-symbol test to both sides reduces the claim to `canonBits_bits`, which says that every natural number’s binary expansion has last-symbol test true.

**Key facts.** `Turing.MachineFormat.canonBits_of_last`, `Turing.MachineFormat.canonBits_bits`.
