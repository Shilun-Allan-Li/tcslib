<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Sweep.lean :: Turing.FinTM.indexedFold_block_reverse -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Indexed reverse-block transduction

**Claim.** Sweeping through the indexed cells in decreasing order produces the table of first components of the local-rule values and the reversed block of their second components.

**Proof.** Apply the indexed-fold formula to the list of indices `List.finRange k` in reverse order. This list has no repeated indices. The formula says that each index in the list receives the first component of its local-rule value, while indices outside the list retain their original table value; it also returns the corresponding list of second components in the same index order. Every element of `Fin k` occurs in `List.finRange k`, so the updated table is exactly the function of first components displayed in the claim. Rewriting the map of a reversed list as the reverse of the mapped list identifies the returned block with the stated reversed block of second components.

**Key facts.** `Turing.FinTM.indexedFold`.
