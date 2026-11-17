<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyTableau.lean :: Complexity.length_tableauGadgets -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Number of Tableau Gadgets

**Claim.** For every finite-state Turing machine $M$ over the binary alphabet, the list of tableau gadgets has length equal to the number of possible snapshots of $M$ plus one.

**Proof.** The gadget list is formed by mapping one gadget for each index in the range of length one more than the snapshot count. Mapping contributes one entry per index, so its length is the range length, namely the snapshot count plus one.
